import OAI.Computability.WitnessedChoice.CountingTransfer

namespace OAI


namespace WitnessedSeparation.Interpretations

noncomputable section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (Domain (d i)))

variable (e : ∀ i, (S i).Carrier → Domain (d i)) (he : ∀ i, Function.Injective (e i))

variable {m B : ℕ} (I : Interpretation R T)

def EncodedDomain : ∀ i, (Fin 2 → Domain (d i)) → Prop := fun i v =>
  ∃ p : I.Domain (S i), v 0 = e i p.val.1 ∧ v 1 = e i p.val.2

def EncodedLink : ∀ i, (Fin 4 → Domain (d i)) → Prop := fun i v =>
  ∃ p q : I.Domain (S i), v 0 = e i p.val.1 ∧ v 1 = e i p.val.2 ∧
    v 2 = e i q.val.1 ∧ v 3 = e i q.val.2 ∧ Reachability.Link (I.link (S i)) p q

def EncodedClass : ∀ i, (Fin 4 → Domain (d i)) → Prop := fun i v =>
  ∃ p q : I.Domain (S i), v 0 = e i p.val.1 ∧ v 1 = e i p.val.2 ∧
    v 2 = e i q.val.1 ∧ v 3 = e i q.val.2 ∧ Quotient.mk (I.classSetoid (S i)) p = Quotient.mk _ q

variable (U : ∀ i, Domain (d i) → Prop) (hU : ∀ i x, U i x ↔ ∃ a, e i a = x)

variable (hdu : UniformDefinable C m 1 (fun i v => U i (v 0)))

variable (δ : ∀ i, (Fin 2 → Domain (d i)) → Prop) (hdδ : UniformDefinable C m 2 δ)

variable (hδ : ∀ i v, δ i (e i ∘ v) ↔ I.domain.eval (S i) v)

include hU hdu hdδ hδ

theorem uniform_domain : UniformDefinable C m 2 (EncodedDomain S e I) := by
  have h₁ : UniformDefinable C m 2 (fun i v => U i (v 0)) := by simpa using hdu.reindex (![0] : Fin 1 → Fin 2)
  have h₂ : UniformDefinable C m 2 (fun i v => U i (v 1)) := by simpa using hdu.reindex (![1] : Fin 1 → Fin 2)
  apply (h₁.and (h₂.and hdδ)).congr
  intro i v
  constructor
  · rintro ⟨h₁,h₂,hv⟩
    obtain ⟨a,ha⟩ := (hU i (v 0)).mp h₁
    obtain ⟨b,hb⟩ := (hU i (v 1)).mp h₂
    have hvv : e i ∘ ![a,b] = v := by ext k; fin_cases k <;> simp [ha,hb]
    exact ⟨⟨(a,b),(hδ i _).mp (by rw [hvv]; exact hv)⟩,ha.symm,hb.symm⟩
  · rintro ⟨p,h₁,h₂⟩
    have hvv : e i ∘ ![p.val.1,p.val.2] = v := by ext k; fin_cases k <;> simp [h₁,h₂]
    refine ⟨(hU i _).mpr ⟨p.val.1,h₁.symm⟩,(hU i _).mpr ⟨p.val.2,h₂.symm⟩,?_⟩
    rw [← hvv]
    exact (hδ i _).mpr p.property

omit hU hdu hdδ hδ

variable (hdom : UniformDefinable C m 2 (EncodedDomain S e I))

variable (η : ∀ i, (Fin 4 → Domain (d i)) → Prop) (hdη : UniformDefinable C m 4 η)

variable (hη : ∀ i v, η i (e i ∘ v) ↔ I.identify.eval (S i) v)

include he hdom hdη hη

theorem uniform_link : UniformDefinable C m 4 (EncodedLink S e I) := by
  have h₁ := hdom.reindex (![0,1] : Fin 2 → Fin 4)
  have h₂ := hdom.reindex (![2,3] : Fin 2 → Fin 4)
  have heq : UniformDefinable C m 4 (fun _ v => v 0 = v 2 ∧ v 1 = v 3) :=
    (UniformDefinable.equal 0 2).and (UniformDefinable.equal 1 3)
  have ht := hdη.reindex (![2,3,0,1] : Fin 4 → Fin 4)
  apply (h₁.and (h₂.and (heq.or (hdη.or ht)))).congr
  intro i v
  constructor
  · rintro ⟨⟨p,hp₁,hp₂⟩,⟨q,hq₁,hq₂⟩,hr⟩
    refine ⟨p,q,hp₁,hp₂,hq₁,hq₂,?_⟩
    rcases hr with ⟨he₁,he₂⟩ | hr | hr
    · exact Or.inl (Subtype.ext (Prod.ext (he i (hp₁.symm.trans (he₁.trans hq₁)))
        (he i (hp₂.symm.trans (he₂.trans hq₂)))))
    · have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] = v := by
        funext k; fin_cases k
        · exact hp₁.symm
        · exact hp₂.symm
        · exact hq₁.symm
        · exact hq₂.symm
      exact Or.inr (Or.inl ((hη i _).mp (by rw [hvv]; exact hr)))
    · have hvv : e i ∘ ![q.val.1,q.val.2,p.val.1,p.val.2] = v ∘ ![2,3,0,1] := by
        funext k; fin_cases k
        · exact hq₁.symm
        · exact hq₂.symm
        · exact hp₁.symm
        · exact hp₂.symm
      exact Or.inr (Or.inr ((hη i _).mp (by rw [hvv]; exact hr)))
  · rintro ⟨p,q,hp₁,hp₂,hq₁,hq₂,hr⟩
    refine ⟨⟨p,hp₁,hp₂⟩,⟨q,hq₁,hq₂⟩,?_⟩
    rcases hr with rfl | hr | hr
    · exact Or.inl ⟨hp₁.trans hq₁.symm,hp₂.trans hq₂.symm⟩
    · have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] = v := by
        funext k; fin_cases k
        · exact hp₁.symm
        · exact hp₂.symm
        · exact hq₁.symm
        · exact hq₂.symm
      exact Or.inr (Or.inl (by rw [← hvv]; exact (hη i _).mpr hr))
    · have hvv : e i ∘ ![q.val.1,q.val.2,p.val.1,p.val.2] = v ∘ ![2,3,0,1] := by
        funext k; fin_cases k
        · exact hq₁.symm
        · exact hq₂.symm
        · exact hp₁.symm
        · exact hp₂.symm
      exact Or.inr (Or.inr (by rw [← hvv]; exact (hη i _).mpr hr))

omit hdom hdη hη

variable (hlink : UniformDefinable C m 4 (EncodedLink S e I))

include hlink

theorem uniform_class (hm : 6 ≤ m) (hB : ∀ i, Nat.card (S i).Carrier ≤ B) :
    UniformDefinable C m 4 (EncodedClass S e I) := by
  apply (Counting.uniform_pairReach C (EncodedLink S e I) hlink hm (B^2)).congr
  intro i v
  have hinj : Function.Injective (fun p : I.Domain (S i) => (e i p.val.1,e i p.val.2)) := by
    intro p q hpq
    exact Subtype.ext (Prod.ext (he i (congrArg Prod.fst hpq)) (he i (congrArg Prod.snd hpq)))
  have hc : Fintype.card (I.Domain (S i)) ≤ B^2 := by
    apply le_trans (Fintype.card_subtype_le _)
    rw [Fintype.card_prod,← Nat.card_eq_fintype_card]
    simpa only [pow_two] using Nat.mul_self_le_mul_self (hB i)
  have h := Counting.pairReach_eqv (I.Domain (S i)) (I.link (S i))
    (fun p => e i p.val.1) (fun p => e i p.val.2) hinj (EncodedLink S e I i)
    (fun _ => Iff.rfl) (B^2) hc v
  have heq : PairReach (EncodedLink S e I) (B^2) i v =
      PairReach (fun _ : Unit => EncodedLink S e I i) (B^2) () v := by
    clear h
    generalize B^2 = t
    induction t generalizing v with
    | zero => rfl
    | succ t ih => simp only [PairReach,ih]
  rw [heq,h]
  unfold EncodedClass
  apply exists_congr
  intro p
  apply exists_congr
  intro q
  refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
    and_congr_right (fun _ => ?_))))
  change (I.classSetoid (S i)).r p q ↔ _
  exact Quotient.eq.symm

end





noncomputable section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (Domain (d i)))

variable (e : ∀ i, (S i).Carrier → Domain (d i)) (he : ∀ i, Function.Injective (e i))

variable {m : ℕ} (I : Interpretation R T)

def EncodedPayload : ∀ i, (Fin 3 → Domain (d i)) → Prop := fun i v =>
  ∃ p : I.Domain (S i), v 1 = e i p.val.1 ∧ v 2 = e i p.val.2 ∧
    (v 0).val = payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p)

def EncodedRep (j : ℕ) : ∀ i, (Fin 3 → Domain (d i)) → Prop := fun i v =>
  ∃ p : I.Domain (S i), v 1 = e i p.val.1 ∧ v 2 = e i p.val.2 ∧
    (v 0).val = vertexCode I (S i) (Subtype.val ∘ e i) j (Quotient.mk _ p)

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable C m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable C m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m)

variable (hdom : UniformDefinable C m 2 (EncodedDomain S e I))

variable (hclass : UniformDefinable C m 4 (EncodedClass S e I))

variable (hpairs : ∀ i (p : I.Domain (S i)), pair (e i p.val.1).val (e i p.val.2).val ∈ d i)

include he hd hmem hset hm hdom hclass hpairs

theorem uniform_payload : UniformDefinable C m 3 (EncodedPayload S e I) := by
  have hc := hclass.reindex (![4,5,1,0] : Fin 4 → Fin 6)
  have hp := (HFCoding.uniform_pair C hmem hset hm hd).reindex (![2,1,0] : Fin 3 → Fin 6)
  have hr := ((hc.and hp).ex (by omega)).ex (by omega)
  have hmem' := hmem.reindex (![0,1] : Fin 2 → Fin 4)
  have hall := (hmem'.iff hr).all (by omega)
  have hs := hset.reindex (![0] : Fin 1 → Fin 3)
  have hdo := hdom.reindex (![1,2] : Fin 2 → Fin 3)
  apply (hs.and (hdo.and hall)).congr
  intro i v
  change (isSet (v 0).val = true ∧ EncodedDomain S e I i ![v 1,v 2] ∧
    ∀ z : Domain (d i), z.val ∈ (v 0).val ↔ ∃ b₁ b₂ : Domain (d i),
      EncodedClass S e I i ![v 1,v 2,b₁,b₂] ∧ z.val = pair b₁.val b₂.val) ↔ _
  constructor
  · rintro ⟨hs,⟨p,hp₁,hp₂⟩,h⟩
    refine ⟨p,hp₁,hp₂,?_⟩
    apply ext_sets hs (isSet_ofFinset _)
    intro z
    change z ∈ (v 0).val ↔ z ∈ payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p)
    rw [mem_payload]
    constructor
    · intro hz
      obtain ⟨b₁,b₂,⟨p',q,hp'₁,hp'₂,hq₁,hq₂,hpq⟩,hzq⟩ :=
        (h ⟨z,hd i _ (v 0).property _ hz⟩).mp hz
      have hpp : p = p' := Subtype.ext (Prod.ext (he i (hp₁.symm.trans hp'₁)) (he i (hp₂.symm.trans hp'₂)))
      subst p'
      change b₁ = e i q.val.1 at hq₁
      change b₂ = e i q.val.2 at hq₂
      exact ⟨q,hpq.symm,by simpa only [hq₁,hq₂,Function.comp_apply] using hzq⟩
    · rintro ⟨q,hqp,rfl⟩
      have hz := hpairs i q
      exact (h ⟨_,hz⟩).mpr ⟨e i q.val.1,e i q.val.2,
        ⟨p,q,hp₁,hp₂,rfl,rfl,hqp.symm⟩,rfl⟩
  · rintro ⟨p,hp₁,hp₂,hv⟩
    refine ⟨by rw [hv]; exact isSet_ofFinset _,⟨p,hp₁,hp₂⟩,?_⟩
    intro z
    rw [hv,mem_payload]
    constructor
    · rintro ⟨q,hqp,hzq⟩
      exact ⟨e i q.val.1,e i q.val.2,⟨p,q,hp₁,hp₂,rfl,rfl,hqp.symm⟩,hzq⟩
    · rintro ⟨b₁,b₂,⟨p',q,hp'₁,hp'₂,hq₁,hq₂,hpq⟩,hzq⟩
      have hpp : p = p' := Subtype.ext (Prod.ext (he i (hp₁.symm.trans hp'₁)) (he i (hp₂.symm.trans hp'₂)))
      subst p'
      change b₁ = e i q.val.1 at hq₁
      change b₂ = e i q.val.2 at hq₂
      exact ⟨q,hpq.symm,by simpa only [hq₁,hq₂,Function.comp_apply] using hzq⟩

end





noncomputable section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (Domain (d i)))

variable (e : ∀ i, (S i).Carrier → Domain (d i))

variable {m : ℕ} (I : Interpretation R T)

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable C m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable C m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m) (hpure : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (hpayload : UniformDefinable C m 3 (EncodedPayload S e I))

include hd hmem hset hm hpure hpayload

theorem uniform_rep (j : ℕ) : UniformDefinable C m 3 (EncodedRep S e I j) := by
  have ho := (HFCoding.uniform_ordinal C hmem hset hm hd hpure j).reindex (![1] : Fin 1 → Fin 5)
  have hs := hpayload.reindex (![0,3,4] : Fin 3 → Fin 5)
  have hp := (HFCoding.uniform_pair C hmem hset hm hd).reindex (![2,1,0] : Fin 3 → Fin 5)
  apply (((ho.and (hs.and hp)).ex (by omega)).ex (by omega)).congr
  intro i v
  change (∃ o S' : Domain (d i), o.val = ordinal j ∧ EncodedPayload S e I i ![S',v 1,v 2] ∧
    (v 0).val = pair o.val S'.val) ↔ _
  constructor
  · rintro ⟨o,S',ho,⟨p,hp₁,hp₂,hS⟩,hx⟩
    change S'.val = payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p) at hS
    exact ⟨p,hp₁,hp₂,by simpa only [vertexCode,ho,hS] using hx⟩
  · rintro ⟨p,hp₁,hp₂,hx⟩
    let pl := payload I (S i) (Subtype.val ∘ e i) (Quotient.mk _ p)
    have hp : pl ∈ d i := by
      have hdbl : double (ordinal j) pl ∈ d i := hd i _ (v 0).property _ (by rw [hx]; simp [vertexCode,pair,pl])
      exact hd i _ hdbl _ (by simp)
    exact ⟨⟨ordinal j,hpure i j⟩,⟨pl,hp⟩,rfl,⟨p,hp₁,hp₂,rfl⟩,hx⟩

omit hd hmem hset hpure hpayload

variable (j : ℕ) (hrep : UniformDefinable C m 3 (EncodedRep S e I j))

include hrep

def EncodedUniverse : ∀ i, (Fin 1 → Domain (d i)) → Prop := fun i v =>
  ∃ x : I.Vertex (S i), (v 0).val = vertexCode I (S i) (Subtype.val ∘ e i) j x

theorem uniform_universe : UniformDefinable C m 1 (EncodedUniverse S e I j) := by
  have hr := hrep.reindex (![2,1,0] : Fin 3 → Fin 3)
  apply ((hr.ex (by omega)).ex (by omega)).congr
  intro i v
  change (∃ a b, EncodedRep S e I j i ![v 0,a,b]) ↔ _
  constructor
  · rintro ⟨a,b,p,_,_,hx⟩
    exact ⟨Quotient.mk _ p,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨p,rfl⟩ := Quotient.exists_rep x
    exact ⟨e i p.val.1,e i p.val.2,p,rfl,rfl,hx⟩

def EncodedStateRelation (r : T) : ∀ i, (Fin 2 → Domain (d i)) → Prop := fun i v =>
  ∃ x y : I.Vertex (S i), (v 0).val = vertexCode I (S i) (Subtype.val ∘ e i) j x ∧
    (v 1).val = vertexCode I (S i) (Subtype.val ∘ e i) j y ∧ (I.apply (S i)).rel r x y = true

variable (ρ : ∀ i, (Fin 4 → Domain (d i)) → Prop)

variable (hdρ : UniformDefinable C m 4 ρ)

include hdρ

theorem uniform_stateRelation (r : T)
    (hρ : ∀ i v, ρ i (e i ∘ v) ↔ (I.relation r).eval (S i) v) :
    UniformDefinable C m 2 (EncodedStateRelation S e I j r) := by
  have hx := hrep.reindex (![4,3,2] : Fin 3 → Fin 6)
  have hy := hrep.reindex (![5,1,0] : Fin 3 → Fin 6)
  have hr := hdρ.reindex (![3,2,1,0] : Fin 4 → Fin 6)
  apply (((((hx.and (hy.and hr)).ex (by omega)).ex (by omega)).ex (by omega)).ex (by omega)).congr
  intro i v
  have hvec (a₁ a₂ b₁ b₂ : Domain (d i)) :
      Fin.cons b₂ (Fin.cons b₁ (Fin.cons a₂ (Fin.cons a₁ v))) ∘ ![3,2,1,0] = ![a₁,a₂,b₁,b₂] := by
    funext k; fin_cases k <;> rfl
  simp only [hvec]
  change (∃ a₁ a₂ b₁ b₂, EncodedRep S e I j i ![v 0,a₁,a₂] ∧
    EncodedRep S e I j i ![v 1,b₁,b₂] ∧ ρ i ![a₁,a₂,b₁,b₂]) ↔ _
  constructor
  · rintro ⟨a₁,a₂,b₁,b₂,⟨p,hp₁,hp₂,hx⟩,⟨q,hq₁,hq₂,hy⟩,hr⟩
    refine ⟨Quotient.mk _ p,Quotient.mk _ q,hx,hy,?_⟩
    simp only [Interpretation.apply,decide_eq_true_eq]
    refine ⟨p,q,rfl,rfl,?_⟩
    have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] = ![a₁,a₂,b₁,b₂] := by
      funext k; fin_cases k
      · exact hp₁.symm
      · exact hp₂.symm
      · exact hq₁.symm
      · exact hq₂.symm
    exact (hρ i _).mp (by rw [hvv]; exact hr)
  · rintro ⟨x,y,hx,hy,hxy⟩
    simp only [Interpretation.apply,decide_eq_true_eq] at hxy
    obtain ⟨p,q,hp,hq,hr⟩ := hxy
    refine ⟨e i p.val.1,e i p.val.2,e i q.val.1,e i q.val.2,
      ⟨p,rfl,rfl,by change (v 0).val = _; rw [hp]; exact hx⟩,
      ⟨q,rfl,rfl,by change (v 1).val = _; rw [hq]; exact hy⟩,?_⟩
    have hvv : e i ∘ ![p.val.1,p.val.2,q.val.1,q.val.2] =
        ![e i p.val.1,e i p.val.2,e i q.val.1,e i q.val.2] := by funext k; fin_cases k <;> rfl
    rw [← hvv]
    exact (hρ i _).mpr hr

end





noncomputable section

open Classical Counting HFCoding Hereditary

variable {ι R T L : Type} {D : ι → Type}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (D i))

variable (e : ∀ i, (S i).Carrier → D i) {m B : ℕ}

structure StateDefinable (m : ℕ) : Prop where
  domainDef : UniformDefinable C m 1 (fun i v => ∃ a, e i a = v 0)
  relations : ∀ r, UniformDefinable C m 2 (fun i v => ∃ a b,
    e i a = v 0 ∧ e i b = v 1 ∧ (S i).rel r a b = true)

theorem StateDefinable.translate (h : StateDefinable S C e m) (he : ∀ i, Function.Injective (e i))
    (hB : ∀ i, Nat.card (S i).Carrier ≤ B) {k : ℕ} (φ : Formula R k) (hw : φ.scopedWidth < m) :
    ∃ Q : ∀ i, (Fin k → D i) → Prop, UniformDefinable C m k Q ∧
      ∀ i v, Q i (e i ∘ v) ↔ φ.eval (S i) v := by
  apply uniform_translate S C e he (fun i x => ∃ a, e i a = x) (fun _ _ => Iff.rfl)
    (fun r i x y => ∃ a b, e i a = x ∧ e i b = y ∧ (S i).rel r a b = true)
    _ h.domainDef h.relations hB φ hw
  intro r i a b
  constructor
  · rintro ⟨a',b',ha,hb,hr⟩
    simpa only [he i ha,he i hb] using hr
  · exact fun hr => ⟨a,b,rfl,rfl,hr⟩

variable {A : ι → Type} {d : ∀ i, Set (HF (A i))}

variable (H : ∀ i, Counting.Structure L (Domain (d i)))

variable (f : ∀ i, (S i).Carrier → Domain (d i)) (hf : ∀ i, Function.Injective (f i))

variable (I : Interpretation R T) (j : ℕ)

variable (hc : ∀ i x, vertexCode I (S i) (Subtype.val ∘ f i) j x ∈ d i)

def nextCode (i : ι) (x : (I.apply (S i)).Carrier) : Domain (d i) :=
  ⟨vertexCode I (S i) (Subtype.val ∘ f i) j x,hc i x⟩

include hf in
theorem nextCode_injective (i : ι) : Function.Injective (nextCode S f I j hc i) := by
  intro x y hxy
  exact vertexCode_injective I (S i) (Subtype.val ∘ f i) (Subtype.val_injective.comp (hf i)) j
    (congrArg Subtype.val hxy)

include hf

theorem StateDefinable.apply (h : StateDefinable S H f m)
    (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)
    (hmem : UniformDefinable H m 2 (fun _ v => (v 0).val ∈ (v 1).val))
    (hset : UniformDefinable H m 1 (fun _ v => isSet (v 0).val = true))
    (hm : 6 ≤ m) (hpure : ∀ i k, ordinal (A := A i) k ∈ d i)
    (hpairs : ∀ i (p : I.Domain (S i)), pair (f i p.val.1).val (f i p.val.2).val ∈ d i)
    (hB : ∀ i, Nat.card (S i).Carrier ≤ B)
    (hwδ : I.domain.scopedWidth < m) (hwη : I.identify.scopedWidth < m)
    (hwρ : ∀ r, (I.relation r).scopedWidth < m) :
    StateDefinable (fun i => I.apply (S i)) H (nextCode S f I j hc) m := by
  obtain ⟨δ,hdδ,hδ⟩ := h.translate S H f hf hB I.domain hwδ
  obtain ⟨η,hdη,hη⟩ := h.translate S H f hf hB I.identify hwη
  have hdom := uniform_domain S H f I (fun i x => ∃ a, f i a = x)
    (fun _ _ => Iff.rfl) h.domainDef δ hdδ hδ
  have hlink := uniform_link S H f hf I hdom η hdη hη
  have hclass := uniform_class S H f hf I hlink hm hB
  have hpay := uniform_payload S H f hf I hd hmem hset hm hdom hclass hpairs
  have hrep := uniform_rep S H f I hd hmem hset hm hpure hpay j
  constructor
  · apply (uniform_universe S H f I hm j hrep).congr
    intro i v
    exact exists_congr (fun x => ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩)
  · intro r
    obtain ⟨ρ,hdρ,hρ⟩ := h.translate S H f hf hB (I.relation r) (hwρ r)
    apply (uniform_stateRelation S H f I hm j hrep ρ hdρ r hρ).congr
    intro i v
    apply exists_congr
    intro x
    apply exists_congr
    intro y
    exact and_congr (⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩)
      (and_congr (⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩) Iff.rfl)

end

end WitnessedSeparation.Interpretations



namespace WitnessedSeparation.Interpretations.Program

noncomputable section

open Classical Counting HFCoding Hereditary Finset

variable {ι R L : Type} (P : Program R)

theorem exists_width : ∃ m : ℕ, 6 ≤ m ∧
    P.init.domain.scopedWidth < m ∧ P.init.identify.scopedWidth < m ∧
    (∀ r, (P.init.relation r).scopedWidth < m) ∧
    P.step.domain.scopedWidth < m ∧ P.step.identify.scopedWidth < m ∧
    (∀ r, (P.step.relation r).scopedWidth < m) ∧
    P.halt.scopedWidth < m ∧ P.output.scopedWidth < m := by
  let := P.stateFinite
  let b : ℕ := univ.sup (fun r => max (P.init.relation r).scopedWidth (P.step.relation r).scopedWidth)
  let m := 7 + P.init.domain.scopedWidth + P.init.identify.scopedWidth + b +
    P.step.domain.scopedWidth + P.step.identify.scopedWidth + P.halt.scopedWidth + P.output.scopedWidth
  have hb (r) : max (P.init.relation r).scopedWidth (P.step.relation r).scopedWidth ≤ b :=
    le_sup (f := fun r => max (P.init.relation r).scopedWidth (P.step.relation r).scopedWidth) (mem_univ r)
  refine ⟨m,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | (intro r; have h := hb r; dsimp [m]; omega) | (dsimp [m]; omega)

variable (S : ι → Structure R) {d : ∀ i, Set (HF (S i).Carrier)}

variable (C : ∀ i, Counting.Structure L (Domain (d i)))

variable {B K m : ℕ}

theorem family_mono_le (A : Structure R) (B : ℕ) {j k : ℕ} (h : j ≤ k) :
    P.family A B j ⊆ P.family A B k := by
  induction h with
  | refl => exact Subset.rfl
  | @step k h ih => exact ih.trans (P.family_mono A B k)

variable (hfamily : ∀ i x, x ∈ P.family (S i) B K → x ∈ d i)

include hfamily in
theorem code_mem_domain {j : ℕ} (hj : j < K) (i : ι) (a : (P.state (S i) j).Carrier) :
    P.code (S i) j a ∈ d i :=
  hfamily i _ (P.family_mono_le (S i) B (by omega) (P.code_mem_family (S i) B j a))

def stateCode {j : ℕ} (hj : j < K) (i : ι) (a : (P.state (S i) j).Carrier) : Domain (d i) :=
  ⟨P.code (S i) j a,P.code_mem_domain S hfamily hj i a⟩

theorem stateCode_injective {j : ℕ} (hj : j < K) (i : ι) :
    Function.Injective (P.stateCode S hfamily hj i) := by
  intro a b h
  exact P.code_injective (S i) j (congrArg Subtype.val h)

def inputCode (i : ι) (a : (S i).Carrier) : Domain (d i) :=
  ⟨atom a,hfamily i _ (P.atom_mem_family (S i) B K a)⟩

theorem inputCode_injective (i : ι) : Function.Injective (P.inputCode S hfamily i) := by
  intro a b h
  exact atom_injective (congrArg Subtype.val h)

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hmem : UniformDefinable C m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable C m 1 (fun _ v => isSet (v 0).val = true))

variable (hm : 6 ≤ m) (hpure : ∀ i k, ordinal (A := (S i).Carrier) k ∈ d i)

variable (hN : ∀ i, Nat.card (S i).Carrier ≤ B)

variable (hsize : ∀ i j, j < K → Nat.card (P.state (S i) j).Carrier ≤ B)

variable (wiδ : P.init.domain.scopedWidth < m) (wiη : P.init.identify.scopedWidth < m)

variable (wiρ : ∀ r, (P.init.relation r).scopedWidth < m)

variable (wsδ : P.step.domain.scopedWidth < m) (wsη : P.step.identify.scopedWidth < m)

variable (wsρ : ∀ r, (P.step.relation r).scopedWidth < m)

variable (hinput : StateDefinable S C (P.inputCode S hfamily) m)

include hd hmem hset hm hpure hN hsize wiδ wiη wiρ wsδ wsη wsρ hinput

theorem state_definable {j : ℕ} (hj : j < K) :
    StateDefinable (fun i => P.state (S i) j) C (P.stateCode S hfamily hj) m := by
  induction j with
  | zero =>
    have hpairs (i) (p : P.init.Domain (S i)) :
        pair (P.inputCode S hfamily i p.val.1).val (P.inputCode S hfamily i p.val.2).val ∈ d i := by
      apply hfamily i
      apply P.family_mono_le (S i) B (show 1 ≤ K by omega)
      apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨p,mem_univ _,by simp [wrappers,inputCode]⟩
    have hc (i) (x : P.init.Vertex (S i)) :
        vertexCode P.init (S i) (Subtype.val ∘ P.inputCode S hfamily i) 1 x ∈ d i :=
      P.code_mem_domain S hfamily hj i x
    exact hinput.apply S C (P.inputCode S hfamily) (P.inputCode_injective S hfamily) P.init 1 hc
      hd hmem hset hm hpure hpairs hN wiδ wiη wiρ
  | succ j ih =>
    have hj' : j < K := by omega
    have hpairs (i) (p : P.step.Domain (P.state (S i) j)) :
        pair (P.stateCode S hfamily hj' i p.val.1).val (P.stateCode S hfamily hj' i p.val.2).val ∈ d i := by
      apply hfamily i
      apply P.family_mono_le (S i) B (show j+2 ≤ K by omega)
      apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨p,mem_univ _,by simp [wrappers,stateCode]⟩
    have hc (i) (x : P.step.Vertex (P.state (S i) j)) :
        vertexCode P.step (P.state (S i) j) (Subtype.val ∘ P.stateCode S hfamily hj' i) (j+2) x ∈ d i :=
      P.code_mem_domain S hfamily hj i x
    exact (ih hj').apply (fun i => P.state (S i) j) C (P.stateCode S hfamily hj')
      (P.stateCode_injective S hfamily hj') P.step (j+2) hc hd hmem hset hm hpure hpairs
      (fun i => hsize i j hj') wsδ wsη wsρ

end

end WitnessedSeparation.Interpretations.Program



namespace WitnessedSeparation.Interpretations

noncomputable section

open Classical Counting

variable {ι R L : Type} {D : ι → Type}

variable (S : ι → Structure R) (C : ∀ i, Counting.Structure L (D i))

variable (e : ∀ i, (S i).Carrier → D i) {m B : ℕ}

theorem StateDefinable.sentence (h : StateDefinable S C e m) (he : ∀ i, Function.Injective (e i))
    (hB : ∀ i, Nat.card (S i).Carrier ≤ B) (ψ : Formula R 0) (hw : ψ.scopedWidth < m) :
    ∃ φ : Counting.Formula L (Fin m), φ.free = ∅ ∧
      ∀ i v, φ.eval (C i) v ↔ ψ.holds (S i) := by
  obtain ⟨Q,hQ,hψ⟩ := h.translate S C e he hB ψ hw
  obtain ⟨φ,hφ,hφQ⟩ := hQ Fin.elim0
  refine ⟨φ,?_,?_⟩
  · apply Finset.subset_empty.mp
    simpa only [Finset.univ_eq_empty,Finset.image_empty] using hφ
  · intro i v
    have hv : v ∘ (Fin.elim0 : Fin 0 → Fin m) = e i ∘ Fin.elim0 := by funext k; exact k.elim0
    exact (hφQ i v).trans (by rw [hv]; exact hψ i Fin.elim0)

namespace Program

variable {R : Type} (P : Program R)

theorem haltsAt_unique (S : Structure R) {j k : ℕ} (hj : P.haltsAt S j) (hk : P.haltsAt S k) : j = k := by
  rcases lt_trichotomy j k with h|h|h
  · exact False.elim (hk.2 j h hj.1)
  · exact h
  · exact False.elim (hj.2 k h hk.1)

theorem accepts_iff_of_haltsAt (S : Structure R) {j : ℕ} (hj : P.haltsAt S j) :
    P.accepts S ↔ P.output.holds (P.state S j) := by
  constructor
  · rintro ⟨k,hk,hout⟩
    rwa [P.haltsAt_unique S hk hj] at hout
  · exact fun hout => ⟨j,hj,hout⟩

theorem synchronize (S T : Structure R) {j k : ℕ}
    (hj : P.haltsAt S j) (hk : P.haltsAt T k)
    (hhalt : ∀ l ≤ min j k, P.halt.holds (P.state S l) ↔ P.halt.holds (P.state T l))
    (hout : ∀ l ≤ min j k, P.output.holds (P.state S l) ↔ P.output.holds (P.state T l)) :
    j = k ∧ (P.accepts S ↔ P.accepts T) := by
  have heq : j = k := by
    rcases le_total j k with h|h
    · have hh := (hhalt j (by omega)).mp hj.1
      have hkj : k ≤ j := by by_contra h'; exact hk.2 j (by omega) hh
      omega
    · have hh := (hhalt k (by omega)).mpr hk.1
      have hjk : j ≤ k := by by_contra h'; exact hj.2 k (by omega) hh
      omega
  refine ⟨heq,?_⟩
  rw [P.accepts_iff_of_haltsAt S hj,P.accepts_iff_of_haltsAt T hk,← heq]
  exact hout j (by omega)

end Program

end

end WitnessedSeparation.Interpretations



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset Support

variable {n : ℕ}

private theorem four_fibers {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ f₁ f₂ f₃ : α → β) (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (h₃ : Function.Injective f₃) (e : β)
    (p : α → Prop) [DecidablePred p] (hp : ∀ a, p a → f₀ a = e ∨ f₁ a = e ∨ f₂ a = e ∨ f₃ a = e) :
    Fintype.card {a // p a} ≤ 4 := by
  have hcard (f : α → β) (hf : Function.Injective f) :
      (univ.filter (fun a => f a = e)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hf ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  rw [Fintype.card_subtype]
  have hs : univ.filter p ⊆
      ((univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e)) ∪
      univ.filter (fun a => f₂ a = e)) ∪ univ.filter (fun a => f₃ a = e) := by
    intro a ha
    have h := hp a (mem_filter.mp ha).2
    simpa only [mem_union,mem_filter,mem_univ,true_and,or_assoc] using h
  exact (card_le_card hs).trans (le_trans (card_union_le _ _) (by
    have h01 := card_union_le (univ.filter (fun a => f₀ a = e)) (univ.filter (fun a => f₁ a = e))
    have h012 := card_union_le
      (univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e))
      (univ.filter (fun a => f₂ a = e))
    have := hcard f₀ h₀; have := hcard f₁ h₁; have := hcard f₂ h₂; have := hcard f₃ h₃
    omega))

theorem edgeFaces_card_le (e : Edge n) : Fintype.card (EdgeFaces e) ≤ 12 := by
  have hxy : Fintype.card {f : FaceXY n // cycle (.inl f) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXY n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j.castSucc k)
      (fun ⟨i,j,k⟩ => ey i.succ j k) (fun ⟨i,j,k⟩ => ex i j.succ k)
      (fun ⟨i,j,k⟩ => ey i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hxz : Fintype.card {f : FaceXZ n // cycle (.inr (.inl f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i.succ j k) (fun ⟨i,j,k⟩ => ex i j k.succ)
      (fun ⟨i,j,k⟩ => ez i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hyz : Fintype.card {f : FaceYZ n // cycle (.inr (.inr f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceYZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ey i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i j.succ k) (fun ⟨i,j,k⟩ => ey i j k.succ)
      (fun ⟨i,j,k⟩ => ez i j.castSucc k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  unfold EdgeFaces Face
  rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum,
    Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
  omega

def localSizeBound : ℕ := 3^25

theorem localGroup_card_le (e : Edge n) : Fintype.card (LocalGroup e) ≤ localSizeBound := by
  rw [Fintype.card_congr (Support.H.productEquiv (localCycle e)),Fintype.card_prod,
    Fintype.card_fun,Fintype.card_prod]
  have hf := edgeFaces_card_le e
  simp only [Scalar,ZMod.card] at *
  change (3*3)^Fintype.card (EdgeFaces e)*3 ≤ 3^25
  calc
    (3*3)^Fintype.card (EdgeFaces e)*3 ≤ (3*3)^12*3 :=
      Nat.mul_le_mul_right 3 (Nat.pow_le_pow_right (by norm_num) hf)
    _ = 3^25 := by norm_num

theorem configuration_card_le (b : Vertex n → Scalar) (v : Vertex n) :
    Fintype.card (Configuration b v) ≤ localSizeBound^6 := by
  have hi : Function.Injective (fun s : Configuration b v => s.state) :=
    fun s t h => Configuration.ext (congrFun h)
  have hdegree : Fintype.card (IncidentEdges v) ≤ 6 := degree_le_six v
  calc
    Fintype.card (Configuration b v) ≤ Fintype.card (LocalStates v) := Fintype.card_le_of_injective _ hi
    _ = ∏ e : IncidentEdges v, Fintype.card (LocalGroup e.val) := Fintype.card_pi
    _ ≤ ∏ _e : IncidentEdges v, localSizeBound := Finset.prod_le_prod (fun e _ => localGroup_card_le e.val)
    _ = localSizeBound^Fintype.card (IncidentEdges v) := by simp
    _ ≤ localSizeBound^6 := Nat.pow_le_pow_right (by norm_num [localSizeBound]) hdegree

def atomSizeConstant : ℕ := 3*localSizeBound+localSizeBound^6

theorem atom_card_bounds (hn : 1 ≤ n) (b : Vertex n → Scalar) :
    (n+1)^3 ≤ Fintype.card (Atom b) ∧
    Fintype.card (Atom b) ≤ atomSizeConstant*(n+1)^3 := by
  have hv : Fintype.card (Vertex n) = (n+1)^3 := by simp [Vertex]; ring
  have he : Fintype.card (Edge n) ≤ 3*(n+1)^3 := by
    simp only [Edge,EdgeX,EdgeY,EdgeZ,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    nlinarith
  constructor
  · rw [← hv]
    apply Fintype.card_le_of_injective (fun v : Vertex n => (.inr ⟨v,someConfiguration hn b v⟩ : Atom b))
    intro v w h
    exact congrArg Sigma.fst (Sum.inr.inj h)
  · change Fintype.card ((Σ e : Edge n, LocalGroup e) ⊕ (Σ v : Vertex n, Configuration b v)) ≤ _
    rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sigma, Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card]
    calc
      (∑ e : Edge n, Fintype.card (LocalGroup e))+
          ∑ v : Vertex n, Fintype.card (Configuration b v) ≤
          (∑ _e : Edge n, localSizeBound)+∑ _v : Vertex n, localSizeBound^6 :=
        add_le_add (sum_le_sum (fun e _ => localGroup_card_le e))
          (sum_le_sum (fun v _ => configuration_card_le b v))
      _ = Fintype.card (Edge n)*localSizeBound+Fintype.card (Vertex n)*localSizeBound^6 := by simp
      _ ≤ (3*(n+1)^3)*localSizeBound+(n+1)^3*localSizeBound^6 := by
        rw [hv]
        exact add_le_add (Nat.mul_le_mul_right _ he) (le_refl _)
      _ = atomSizeConstant*(n+1)^3 := by unfold atomSizeConstant; ring

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical

variable {A G : Type*} [Group G] [MulAction G A] {s : ℕ}

theorem hereditary_iff {x : HF A} : HereditarilySupported (G := G) s x ↔
    Supported (G := G) s x ∧ ∀ y, y ∈ x → HereditarilySupported (G := G) s y := by
  constructor
  · intro h
    exact ⟨h x .refl,fun y hy z hz => h z (hz.tail hy)⟩
  · rintro ⟨h,hm⟩ y hy
    cases hy with
    | refl => exact h
    | tail hz hzx => exact hm _ hzx _ hz

theorem hereditary_transitive {x y : HF A} (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := (hereditary_iff.mp hx).2 y hy

theorem ordinal_hereditary [Nonempty A] (s j : ℕ) :
    HereditarilySupported (G := G) s (ordinal (A := A) j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    apply hereditary_iff.mpr
    constructor
    · refine ⟨fun _ => Classical.choice (inferInstance : Nonempty A),?_⟩
      intro g _
      exact map_ordinal (fun a => g • a) j
    · intro y hy
      obtain ⟨k,hk,rfl⟩ := (mem_ordinal y j).mp hy
      exact ih k hk

end

end WitnessedSeparation.Hereditary



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Interpretations

variable {n : ℕ} (b : Vertex n → Scalar)

abbrev programInput : Interpretations.Structure Symbol where
  Carrier := Atom b
  finite := inferInstance
  rel := (atomInput b).rel

def programActionIso (g : BoxGroup n) : (programInput b).Iso (programInput b) where
  equiv := (actionIso (b := b) g).toEquiv
  rel r x y := ((actionIso (b := b) g).rel_eq r x y).symm

variable (P : Interpretations.Program Symbol)

theorem trace_supported (hn : 1 ≤ n) (B K N : ℕ) (hB : 2 ≤ B) (hK : K ≤ B)
    (hN : Nat.card (Atom b) ≤ B) (hNpos : 0 < N)
    (hsize : ∀ j < K, Nat.card (P.state (programInput b) j).Carrier ≤ B)
    (q : ℝ) (hq : 0 ≤ q) (hpoly : (9*B^3 : ℝ) ≤ (N : ℝ)^q) :
    ∀ x ∈ P.family (programInput b) B K,
      HereditarilySupported (G := CentralGroup n) ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ x := by
  obtain ⟨hc,ht,hi⟩ := P.trace_family (programInput b) B K hB hK hN hsize
  have hInv : ∀ g : BoxGroup n, ∀ x ∈ P.family (programInput b) B K,
      g • x ∈ P.family (programInput b) B K := by
    intro g x hx
    exact hi (programActionIso b g) x hx
  exact invariant_family_hereditarily_supported hn _ hInv ht N hNpos q hq
    (le_trans (by exact_mod_cast hc) hpoly)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

def programDomain (i : ι) : Set (HF (Atom (bs i))) := HereditarilySupported (G := CentralGroup n) s

def programHF (i : ι) : Counting.Structure (Forms.HFRelation AnalysisSymbol) (Domain (programDomain bs (s := s) i)) :=
  Forms.hfStructure (analysisStructure (bs i))

theorem program_domain_transitive (i : ι) :
    ∀ x ∈ programDomain bs (s := s) i, ∀ y, y ∈ x → y ∈ programDomain bs (s := s) i :=
  fun _ hx _ hy => hereditary_transitive hx hy

theorem program_mem_uniform : UniformDefinable (programHF bs (s := s)) m 2
    (fun _ v => (v 0).val ∈ (v 1).val) :=
  UniformDefinable.relation (S := programHF bs (s := s)) .mem 0 1

theorem program_set_uniform : UniformDefinable (programHF bs (s := s)) m 1
    (fun _ v => isSet (v 0).val = true) := by
  apply (UniformDefinable.relation (S := programHF bs (s := s)) .atom 0 0).neg.congr
  intro i v
  change (¬ isSet (v 0).val = false) ↔ _
  cases isSet (v 0).val <;> simp

theorem program_pure (hn : 1 ≤ n) (i : ι) (k : ℕ) : ordinal k ∈ programDomain bs (s := s) i := by
  let := atom_nonempty hn (bs i)
  exact ordinal_hereditary s k

variable {B K : ℕ}

variable (hfamily : ∀ i x, x ∈ P.family (programInput (bs i)) B K → x ∈ programDomain bs (s := s) i)

theorem program_input_definable : StateDefinable (fun i => programInput (bs i)) (programHF bs)
    (P.inputCode (fun i => programInput (bs i)) hfamily) m := by
  constructor
  · apply (UniformDefinable.relation (S := programHF bs) .atom 0 0).congr
    intro i v
    change isSet (v 0).val = false ↔ ∃ a, _
    constructor
    · intro hx
      rcases atom_or_set (v 0).val with ⟨a,ha⟩|ha
      · exact ⟨a,Subtype.ext ha.symm⟩
      · rw [ha,isSet_ofFinset] at hx
        cases hx
    · rintro ⟨a,ha⟩
      rw [← congrArg Subtype.val ha]
      rfl
  · intro r
    apply (UniformDefinable.relation (S := programHF bs) (.base (.input r)) 0 1).congr
    intro i v
    change (∃ a b, (v 0).val = atom a ∧ (v 1).val = atom b ∧ AtomRelation (bs i) r a b) ↔ _
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    refine and_congr ?_ (and_congr ?_ ?_)
    · exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    · exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    · simp [atomInput]

end





noncomputable section

open Classical Hereditary Counting HFCoding Interpretations

variable {n B K N m M : ℕ} (P : Program Symbol) (vstar : Vertex n)

def twoCharges : Bool → Vertex n → Scalar
  | false => 0
  | true => Pi.single vstar 1

variable (hn : 1 ≤ n) (hB : 2 ≤ B) (hK : K ≤ B) (hNpos : 0 < N)

variable (hN : ∀ i, Nat.card (Atom (twoCharges vstar i)) ≤ B)

variable (hsize : ∀ i j, j < K → Nat.card (P.state (programInput (twoCharges vstar i)) j).Carrier ≤ B)

variable (q : ℝ) (hq : 0 ≤ q) (hpoly : (9*B^3 : ℝ) ≤ (N : ℝ)^q)

variable (hm : 6 ≤ m)

variable (wiδ : P.init.domain.scopedWidth < m) (wiη : P.init.identify.scopedWidth < m)

variable (wiρ : ∀ r, (P.init.relation r).scopedWidth < m)

variable (wsδ : P.step.domain.scopedWidth < m) (wsη : P.step.identify.scopedWidth < m)

variable (wsρ : ∀ r, (P.step.relation r).scopedWidth < m)

include hn hB hK hNpos hN hsize hq hpoly hm wiδ wiη wiρ wsδ wsη wsρ

theorem stage_sentence_agrees
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    {j : ℕ} (hj : j < K) (ψ : Interpretations.Formula P.StateSymbols 0) (hw : ψ.scopedWidth < m) :
    ψ.holds (P.state (programInput (0 : Vertex n → Scalar)) j) ↔
      ψ.holds (P.state (programInput (Pi.single vstar 1)) j) := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let S := fun i => programInput (twoCharges vstar i)
  let C := programHF (twoCharges vstar) (s := s)
  have hfamily : ∀ i x, x ∈ P.family (S i) B K → x ∈ programDomain (twoCharges vstar) (s := s) i :=
    fun i => trace_supported (twoCharges vstar i) P hn B K N hB hK (hN i) hNpos
      (hsize i) q hq hpoly
  have hd := P.state_definable S C hfamily (program_domain_transitive (twoCharges vstar))
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar)) hm
    (program_pure (twoCharges vstar) hn) hN hsize wiδ wiη wiρ wsδ wsη wsρ
    (program_input_definable P (twoCharges vstar) hfamily) hj
  obtain ⟨φ,hφ,hφψ⟩ := hd.sentence (fun i => P.state (S i) j) C (P.stateCode S hfamily hj)
    (P.stateCode_injective S hfamily hj) (fun i => hsize i j hj) ψ hw
  let v : Fin m → Domain (programDomain (twoCharges vstar) (s := s) false) :=
    fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (programDomain (twoCharges vstar) (s := s) true) :=
    fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  exact (hφψ false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
    hwidth hhom hgiant φ hφ v w).trans (hφψ true w))

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Quantitative

noncomputable section

open Filter Asymptotics Topology

lemma const_little_rpow (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun _ : ℝ => c) =o[atTop] (fun L => L^r) :=
  (isLittleO_const_id_atTop c).comp_tendsto (tendsto_rpow_atTop hr)

lemma power_little_power {a b : ℝ} (hab : a < b) :
    (fun L : ℝ => L^a) =o[atTop] (fun L => L^b) := by
  have h := (isBigO_refl (fun L : ℝ => L^a) atTop).mul_isLittleO (const_little_rpow 1 (sub_pos.mpr hab))
  apply h.congr' (by filter_upwards [] with L; simp)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [← Real.rpow_add hL]
  congr 1
  ring

lemma ceil_little {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (h : f =o[l] g) (h1 : (fun _ => (1:ℝ)) =o[l] g) :
    (fun x => (⌈f x⌉₊ : ℝ)) =o[l] g := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hf,h.bound (show 0 < c/2 by linarith),h1.bound (show 0 < c/2 by linarith)] with x hx hh hconst
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [Real.norm_of_nonneg hx] at hh
  norm_num at hconst
  have hb := Nat.ceil_lt_add_one hx
  simp only [Real.norm_eq_abs] at hh ⊢
  linarith

def radius (C q L : ℝ) : ℕ := ⌈2*L*(q*Real.logb 3 (C*L^3))^2⌉₊

def palette (L : ℝ) : ℕ := ⌊L^((7:ℝ)/4)⌋₊

lemma log_volume_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => q*Real.logb 3 (C*L^3)) =o[atTop] (fun L => L^((1:ℝ)/12)) := by
  have hc := const_little_rpow (Real.log C) (show 0 < (1:ℝ)/12 by norm_num)
  have hl := (isLittleO_log_rpow_atTop (show 0 < (1:ℝ)/12 by norm_num)).const_mul_left 3
  have h := ((hc.add hl).const_mul_left ((q:ℝ)/Real.log 3))
  apply h.congr' _ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  simp only [Real.logb,Real.log_mul (ne_of_gt hC) (ne_of_gt (pow_pos hL 3)),Real.log_pow]
  ring

lemma radius_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
  have hlog := log_volume_little C q hC
  have hsquare := hlog.pow (show 0 < 2 by omega)
  have hlin := (isBigO_refl (fun L : ℝ => L) atTop).mul_isLittleO hsquare
  have hraw : (fun L : ℝ => 2*L*(q*Real.logb 3 (C*L^3))^2) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
    apply (hlin.const_mul_left 2).congr' (by filter_upwards [] with L; ring)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    calc
      L * (L ^ ((1:ℝ)/12)) ^ 2 = L^((1:ℝ)) * L^(((1:ℝ)/12)*2) := by
        rw [Real.rpow_one, Real.rpow_mul hL.le]; norm_num
      _ = L^((7:ℝ)/6) := by rw [← Real.rpow_add hL]; norm_num
  apply ceil_little _ hraw (const_little_rpow 1 (by norm_num))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  positivity

lemma radius_little_palette (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/4)) :=
  (radius_little C q hC).trans (power_little_power (by norm_num))

lemma homogeneity_little (C q m c : ℝ) (hC : 0 < C) :
    (fun L : ℝ => 7*(m*(radius C q L:ℝ))+7*((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1)
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
  have hlin := (radius_little_palette C q hC).const_mul_left (7*m)
  have hsr := (radius_little C q hC).const_mul_left (6*m/c)
  have hp := hsr.rpow (show 0 < (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2))
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
    apply hp.congr' (by filter_upwards [] with L; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := (hlin.add (hp'.const_mul_left 7)).add (const_little_rpow 1 (by norm_num))
  apply h.congr_left
  intro L
  ring

lemma floor_big (a : ℝ) : (fun L : ℝ => (⌊L^a⌋₊:ℝ)) =O[atTop] (fun L => L^a) := by
  apply IsBigO.of_norm_eventuallyLE
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.floor_le (Real.rpow_nonneg hL _)

lemma giant_little (c : ℝ) :
    (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =o[atTop] (fun L => L^3) := by
  have hb := (floor_big ((7:ℝ)/4)).const_mul_left (12/c)
  have hp := hb.rpow (show 0 ≤ (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =O[atTop]
      (fun L => L^((21:ℝ)/8)) := by
    apply hp.congr' (by filter_upwards [] with L; simp only [palette]; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := hp'.trans_isLittleO (power_little_power (a := (21:ℝ)/8) (b := 3) (by norm_num))
  exact h.congr_right (fun L => Real.rpow_natCast L 3)

theorem eventual_bounds (C q c : ℝ) (hC : 0 < C) (hc : 0 < c) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (max 4 (m+1):ℝ)*(radius C q L:ℝ) ≤ (palette L:ℝ) ∧
      7*((max 2 m:ℝ)*(radius C q L:ℝ))+
        7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 ≤ (palette L:ℝ) ∧
      ((12*(palette L:ℝ))/c)^((3:ℝ)/2) < L^3 := by
  have hw := ((radius_little_palette C q hC).const_mul_left (max 4 (m+1):ℝ)).bound
    (show 0 < (1:ℝ)/2 by norm_num)
  have hh := (homogeneity_little C q (max 2 m:ℝ) c hC).bound (show 0 < (1:ℝ)/2 by norm_num)
  have hg := (giant_little c).bound (show 0 < (1:ℝ)/2 by norm_num)
  filter_upwards [hw,hh,hg,eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (show 0 < (7:ℝ)/4 by norm_num)).eventually_ge_atTop 2] with L hw hh hg hL hpow
  have hp : 0 ≤ L^((7:ℝ)/4) := Real.rpow_nonneg hL.le _
  have hs : 0 ≤ (radius C q L:ℝ) := Nat.cast_nonneg _
  have hfl := Nat.lt_floor_add_one (L^((7:ℝ)/4))
  have hn : 0 ≤ 7*((max 2 m:ℝ)*(radius C q L:ℝ))+
      7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 := by positivity
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hp] at hw
  rw [Real.norm_of_nonneg hn,Real.norm_of_nonneg hp] at hh
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (pow_nonneg hL.le 3)] at hg
  change _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _
  refine ⟨by linarith,by linarith,?_⟩
  have hcube := pow_pos hL 3
  linarith

end





def timeExponent (c d : ℕ) := c + 2*d + 2

def traceExponent (c d : ℕ) := 3*timeExponent c d + 4

lemma timeExponent_ge_two (c d : ℕ) : 2 ≤ timeExponent c d := by unfold timeExponent; omega

lemma nat_le_power (N c : ℕ) (hN : 2 ≤ N) : c ≤ N^c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ]
    have hp : 1 ≤ N^c := Nat.one_le_pow _ _ (by omega)
    nlinarith

lemma polynomial_bounds (c d N : ℕ) (hN : 2 ≤ N) :
    2 ≤ N^timeExponent c d ∧ N ≤ N^timeExponent c d ∧
    c*(N+1)^d ≤ N^timeExponent c d ∧
    9*(N^timeExponent c d)^3 ≤ N^traceExponent c d := by
  have hpos : 1 ≤ N := by omega
  have hD := timeExponent_ge_two c d
  have hNB : N ≤ N^timeExponent c d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (show 1 ≤ timeExponent c d by omega)
  refine ⟨le_trans hN hNB,hNB,?_,?_⟩
  · calc
      c*(N+1)^d ≤ N^c*(N^2)^d := Nat.mul_le_mul (nat_le_power N c hN)
        (Nat.pow_le_pow_left (by nlinarith : N+1 ≤ N^2) d)
      _ = N^(c+2*d) := by rw [← pow_mul,← pow_add]
      _ ≤ N^timeExponent c d := Nat.pow_le_pow_right hpos (by unfold timeExponent; omega)
  · calc
      9*(N^timeExponent c d)^3 ≤ N^4*(N^timeExponent c d)^3 := by
        apply Nat.mul_le_mul_right
        have hh := Nat.pow_le_pow_left hN 4
        norm_num at hh
        omega
      _ = N^traceExponent c d := by
        rw [← pow_mul,← pow_add]
        unfold traceExponent
        congr 1
        omega

lemma real_trace_bound (c d N : ℕ) (hN : 2 ≤ N) :
    (9*(N^timeExponent c d)^3 : ℝ) ≤ (N:ℝ)^(traceExponent c d:ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast (polynomial_bounds c d N hN).2.2.2

end WitnessedSeparation.Quantitative



namespace WitnessedSeparation.Interpretations.Program

noncomputable section

open Classical Finset

variable {R : Type} (P : Program R)

lemma stage_le_cost (A : Structure R) (j : ℕ) : j+1 ≤ P.cost A j := by
  unfold cost
  omega

lemma size_le_cost (A : Structure R) {j k : ℕ} (hk : k ≤ j) :
    Nat.card (P.state A k).Carrier ≤ P.cost A j := by
  rw [Nat.card_eq_fintype_card]
  unfold cost
  have h := Finset.single_le_sum (f := fun l => Fintype.card (P.state A l).Carrier)
    (fun l _ => Nat.zero_le _) (show k ∈ Finset.range (j+1) by simpa using hk)
  omega

end

end WitnessedSeparation.Interpretations.Program

end OAI

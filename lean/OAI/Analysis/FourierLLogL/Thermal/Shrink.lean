import OAI.Analysis.FourierLLogL.Compress.Endpoint
import OAI.Analysis.FourierLLogL.Thermal.Power

/-! # Iterated spectral compression -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Real Period Compress.Params

variable {M l : ℕ}
open scoped Classical

def supported (s : Finset (Grid l)) (P : Law (Grid l)) := ∀ i, 0 < P i → i∈s

def evenly (s : Finset (Grid l)) (P : Law (Grid l)) :=
    ∀ i∈s, P i = (s.card:ℝ)⁻¹

lemma exists_uniform_sub {s : Finset (Grid l)} (hs : s.Nonempty) :
    ∃ p : Law (Grid l), supported s p ∧ evenly s p := by
  classical
  have : Nonempty (s:Type) := Finset.Nonempty.to_subtype hs
  let f : s → Grid l := fun x => x.val
  refine ⟨(uniform _).send f, ?_,?_⟩
  · intro i hi; obtain ⟨x,rfl,_⟩ := (send_pos_iff _ _ _).mp hi
    exact x.property
  intro i hi
  rw [send_apply,prob_eq]
  simp_rw [uniform_apply,Fintype.card_coe]
  rw [Finset.sum_eq_single (⟨i,hi⟩:s),ite_eq_left rfl]
  · intro j _ hj
    exact ite_eq_right (fun h => hj (Subtype.ext h))
  simp

lemma represent_law {s : Finset (Grid l)} {P : Law (Grid l)}
    (hp : supported s P) :
    ∃ q : Law s, q.send (fun x => (x:Grid l))=P := by
  obtain ⟨x,hx⟩ := mem_nonempty P
  have hx' := hp x hx
  let f (i : Grid l) : s := if hi : i∈s then ⟨i,hi⟩ else ⟨x,hx'⟩
  refine ⟨P.send f,?_⟩
  rw [send_send]
  rw [send_congr_mem P (Y:=fun x => x),send_id]
  intro y hy
  simp [f,hp y hy]

/-- averaged defect form. -/
def averageCost (hl : l ≤ M) (p : Law (Grid l)) (x : Grid l) : Form M :=
    fun i => p.prob fun y => i = raise hl (y-x)

lemma averageCost_pos (hl : l ≤ M) (p : Law (Grid l)) (x : Grid l) :
    0 ≤ averageCost hl p x := fun _ => prob_nonneg _ _

lemma average_form (hl : l ≤ M) (p : Law (Grid l)) (x : Grid l) (t : Grid M) :
    form (averageCost hl p x) t = p.Ex (fun y => cost (raise hl (y-x)) t) := by
  simp_rw [form,averageCost,prob,← Ex_mul,← Ex_finset_sum]
  congr 1; funext i
  simp only [ite_mul, one_mul,zero_mul]
  simp

def shrinkScale (D : ℝ) (j : ℕ) :=
    300000*D^2*height j^2/(slow j:ℝ)^2

lemma spectral_compression (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ j : ℕ in atTop, ∀ (M l : ℕ) (hl : l ≤ M) (A : Form M)
      (R : ℝ) (hA : 0 ≤ A), 2^(M-l) ≤ R → S M R ≤ A →
      -log (fq hl A hA 0) ≤ D*height j →
      ∀ (s : Finset (Grid l)), s.Nonempty →
        (∀ n : ℕ, n ≤ 2^(2*j) → Compress.lnS (Fin n) (fun x : s => (x:Grid l)) ≤ height j * (j:ℝ)^2) →
        ∀ t : ℝ, height j/(slow j:ℝ)^2 ≤ t → t ≤ D*height j →
        (∀ P : Law (Grid l), supported s P → levelCost hl A P (sLen j) ≤ t) →
        ∃ (x : Grid l) (u : Finset (Grid l)), x∈s ∧ u⊆s ∧ u.Nonempty ∧
          log (s.card:ℝ)-log (u.card:ℝ) ≤ shrinkScale D j/t ∧
          ∀ P : Law (Grid l), supported u P →
            F (A + long j • averageCost hl P x) - F A ≤ 350*t := by
  classical
  filter_upwards [Compress.entropy_compression D hD] with j hj
  intro M l hl A R hA hR hH hp s hs hL t ht ht' hT
  have : Nonempty (s:Type) := Finset.Nonempty.to_subtype hs
  let f : s → Grid l := fun x => x
  obtain ⟨h0,h1,h2,h3,h4,_⟩ := fq_spec hl A hA hR hH
  obtain ⟨x,u,hu,hv,H⟩ := hj s (Grid l) (Grid M) _ _ _ inferInstance _ _ f Subtype.val_injective
    (fq hl A hA) h0 (fq_cost hl A) h1 h2 (label A) (raiseChar hl)
    (by intro t i; rw [raiseChar_eq,norm_chi]) h3 h4 hp hL t ht ht' (by
    intro p
    let P := p.send f
    have HH := (hT P fun i hi => by
      obtain ⟨x,rfl,_⟩ := (send_pos_iff _ _ _).mp hi
      exact x.property)
    have hn (i : Grid M) : 0 < cred A i := by
      unfold cred
      exact div_pos (q_pos_one hA (lt_of_lt_of_le (S_one_pos
        ((one_le_pow₀ (by norm_num : (1:ℝ)≤2)).trans hR)) (hH _)) _) (q_origin_pos _)
    rw [selected_heat _ hl A hn p f,← heat_exp]
    exact exp_monotone (neg_le_neg HH))
  let w := u.image f
  have hw : w⊆s := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact x.property
  refine ⟨x,w,x.property,hw,hu.image f,?_,?_⟩
  · rw [Fintype.card_coe] at hv
    rw [show w.card=u.card from Finset.card_image_of_injective u Subtype.val_injective]
    apply hv.trans; unfold shrinkScale; exact le_of_eq (by ring)
  intro P hP
  obtain ⟨Q,hQ⟩ := represent_law (s:=s) (show supported s P from fun x hx => hw (hP x hx))
  have hU (y) (hy : 0 < Q y) : y∈u := by
    have he : 0 < P (f y) := hQ ▸ Q.send_pos f hy
    obtain ⟨x,hx,H⟩ := Finset.mem_image.mp (hP _ he)
    rwa [Subtype.ext H] at hx
  have He := H Q hU
  let B := averageCost hl P x
  have hX (y : Grid M) :
      exp ((-long j)*Q.Ex (fun i => Compress.defect f (raiseChar hl) i x y)) =
        boltz (long j • B) y := by
    unfold B boltz; rw [form_smul,average_form,← hQ,Ex_send]
    refine congrArg exp ?_; rw [neg_mul]
    simp_rw [Compress.defect,raiseChar_eq,cost,wave]
    rfl
  simp_rw [hX,boltz_mean, Real.exp_le_exp] at He
  change F (A+long j • B)-F A ≤ _
  linarith

lemma choose_compression {hl : l ≤ M} {A : Form M} {T : ℕ} {s : Finset (Grid l)} {b c Z L : ℝ}
    (hc : 0 < c) (hZ : 0 ≤ Z) (hb : c ≤ b)
    (H : ∀ u : Finset (Grid l), u ⊆ s → u.Nonempty →
      ∀ t : ℝ, c ≤ t → t ≤ b →
      (∀ P : Law (Grid l), supported u P → levelCost hl A P T ≤ t) →
      ∃ (x : Grid l) (w : Finset (Grid l)), x∈u ∧ w⊆u ∧ w.Nonempty ∧
          log (u.card:ℝ)-log (w.card:ℝ) ≤ Z/t ∧
          ∀ P : Law (Grid l), supported w P →
            F (A + L • averageCost hl P x) - F A ≤ 350*t)
    (hs : s.Nonempty) (hM : ∀ P : Law (Grid l), supported s P → levelCost hl A P T ≤ b) :
    ∃ (x : Grid l) (w : Finset (Grid l)) (P : Law (Grid l)) (t : ℝ),
      c ≤ t ∧ t ≤ b ∧ x∈s ∧ w⊆s ∧ w.Nonempty ∧ supported w P ∧
      log (s.card:ℝ)-log (w.card:ℝ) ≤ 4*Z/c ∧
      F (A + L • averageCost hl P x) - F A ≤ 350*t ∧
      ((t = c ∧ evenly w P) ∨ t/4 ≤ levelCost hl A P T) := by
  let Good (w : Finset (Grid l)) (x : Grid l) (P : Law (Grid l)) (t : ℝ) : Prop :=
    F (A + L • averageCost hl P x) - F A ≤ 350*t ∧
        ((t=c ∧ evenly w P) ∨ t/4 ≤ levelCost hl A P T)
  have bottom (u : Finset (Grid l)) (hu : u⊆s) (hv : u.Nonempty)
      (ht : ∀ P : Law (Grid l), supported u P → levelCost hl A P T ≤ c) :
      ∃ (x : Grid l) (w : Finset (Grid l)) (P : Law (Grid l)),
        x∈s ∧ w⊆s ∧ w.Nonempty ∧ supported w P ∧
        log (u.card:ℝ)-log (w.card:ℝ) ≤ Z/c ∧ Good w x P c := by
    obtain ⟨x,w,hx,hw,hS,h1,h2⟩ := H u hu hv c le_rfl hb ht
    obtain ⟨P,h3,h4⟩ := exists_uniform_sub hS
    exact ⟨x,w,P,hu hx,Finset.Subset.trans hw hu,hS,h3,h1,h2 _ h3,Or.inl ⟨rfl,h4⟩⟩
  let K := fun (u : Finset (Grid l)) (f : ℝ) => ∃ (x : Grid l)
      (w : Finset (Grid l)) (P : Law (Grid l)) (t : ℝ),
      c ≤ t ∧ t ≤ b ∧ x∈s ∧ w⊆s ∧ w.Nonempty ∧ supported w P ∧
      log (u.card:ℝ)-log (w.card:ℝ) ≤ 4*Z/c-Z/f ∧ Good w x P t
  have HH (n : ℕ) (u : Finset (Grid l)) (hu : u⊆s) (h0 : u.Nonempty)
      (f : ℝ) (hf : c ≤ f) (hB : f ≤ b) (he : f ≤ n*c) (hi : ∀ P : Law (Grid l),
        supported u P → levelCost hl A P T ≤ f) : K u f := by
    induction n generalizing u f with
    | zero => norm_num at he; linarith
    | succ n ih =>
    have hp : 0 < f := lt_of_lt_of_le hc hf
    have h1 : Z/f ≤ Z/c := by gcongr
    have hN : 0 ≤ Z/c := div_nonneg hZ hc.le
    obtain ⟨x,w,hx,hw,hS,hG,hM⟩ := H _ hu h0 f hf hB hi
    by_cases h : ∃ P : Law (Grid l), supported w P ∧ f/4 ≤ levelCost hl A P T
    · rcases h with ⟨P,hP,hE⟩
      exact ⟨x,w,P,f,hf,hB,hu hx,Finset.Subset.trans hw hu,hS,hP,by rw [mul_div_assoc]; linarith,hM _ hP,Or.inr hE⟩
    have h2 (P : Law (Grid l)) (hP : supported w P) : levelCost hl A P T ≤ f/4 :=
      le_of_lt <| lt_of_not_ge fun hh => h ⟨P,hP,hh⟩
    rcases le_total (f/4) c with hy|hy
    · obtain ⟨x,V,P,h1',h2',h3,h4,h5,h6⟩ := bottom w (Finset.Subset.trans hw hu) hS
        (fun x hx => (h2 x hx).trans hy)
      exact ⟨x,V,P,c,le_rfl,hb,h1',h2',h3,h4,by rw [mul_div_assoc]; linarith,h6⟩
    obtain ⟨x,V,P,t,h1',h2',h3,h4,h5,h6,h7,h8⟩ := ih w (Finset.Subset.trans hw hu) hS
      (f/4) hy (by linarith) (by push_cast at he; nlinarith) h2
    rw [show Z/(f/4)=4*(Z/f) by ring] at h7
    exact ⟨x,V,P,t,h1',h2',h3,h4,h5,h6,by linarith [div_nonneg hZ hp.le],h8⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (b/c)
  obtain ⟨x,w,P,t,h1,h2,h3,h4,h5,h6,h7,h8⟩ :=
    HH n s (Finset.Subset.refl _) hs b hb le_rfl ((div_lt_iff₀ hc).mp hn).le hM
  exact ⟨x,w,P,t,h1,h2,h3,h4,h5,h6,h7.trans (sub_le_self _ (div_nonneg hZ (hc.le.trans hb))),h8⟩

end FourierLLogL.Dyadic.Thermal

end OAI

import OAI.Analysis.C0Absorption.Supports

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def SignedBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ) : Prop :=
  ∀ n (ι : Fin n → ℕ), Function.Injective ι → ∀ ε : Fin n → Bool,
    ‖∑ i, realSign (ε i) • m (ι i)‖ ≤ M

namespace SignedBound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ → X} {M : ℝ} (hm : SignedBound m M)

include hm

theorem initial : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M :=
  fun n ε => hm n Fin.val Fin.val_injective ε

theorem subsequence {φ : ℕ → ℕ} (hφ : Function.Injective φ) : SignedBound (m ∘ φ) M :=
  fun n ι hι ε => hm n (φ ∘ ι) (hφ.comp hι) ε

theorem nonneg : 0 ≤ M := by
  simpa using hm.initial 0 (fun i => Fin.elim0 i)

end SignedBound

theorem compatible_detectors_false {S : Type*} [MetricSpace S]
    (L : ℕ → Set (S → ℝ)) (o : S)
    (m : ℕ → TestSpace L o) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → S → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ L h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ) (hd : ∀ i, δ ≤ |completedPairing L o (F i) (m i)|) : False := by
  obtain ⟨C,hC⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨d,hdtriple⟩ := triple_surjective (h,C,0)
  have hKC : K ≤ listConstant d := by
    change K ≤ ((triple d).2.1 : ℝ≥0)+1
    rw [hdtriple]
    exact_mod_cast (show (K : ℝ) ≤ (C : ℝ)+1 by linarith)
  let l (n : ℕ) : AdmissibleList (L (triple d).1) (listConstant d) :=
    ⟨n,fun i => F i,fun i => by simpa only [hdtriple] using hF i,
      fun ε hε => (hLip n ε hε).weaken hKC⟩
  have hExp : (listExponent d).toReal = 2 := by rw [listExponent_toReal,hdtriple]; norm_num
  have hb (i : ℕ) : ∃ A : ℝ≥0, ∀ z : PreSpace L o, |pairing S (F i) z| ≤ A*‖z‖ := by
    let j : Fin (i+1) := ⟨i,Nat.lt_succ_self i⟩
    exact ⟨(squareWeight d)⁻¹,list_test_pairing_bound L o d (l (i+1)) j⟩
  choose A hA using hb
  let u (i : ℕ) : TestSpace L o →ₗ[ℝ] ℝ := (completedTest L o (F i) (A i) (hA i)).toLinearMap
  have hu (i : ℕ) (z : TestSpace L o) : u i z = completedPairing L o (F i) z :=
    completedTest_eq L o _ _ _ _
  apply no_infinite_detectors m u ((squareWeight d : ℝ)^2) M δ
    (sq_pos_of_pos (squareWeight_pos d)) hm.nonneg hδ hm.initial
  · intro n z
    have hl := (completedList_le_sigma L o d (l n) z).trans (completedSigma_le L o d z)
    have heq : ‖completedList L o d (l n) z‖^2 = ∑ i : Fin n, (u i z)^2 := by
      have he := finite_lp_norm_rpow (listExponent d) (by rw [hExp]; norm_num)
        (completedList L o d (l n) z)
      rw [hExp] at he
      simp only [Real.rpow_two,sq_abs] at he
      rw [he]
      apply Finset.sum_congr rfl
      intro i hi
      change (completedList L o d (l n) z i)^2 = (u i z)^2
      rw [completedList_apply,hu]
    have hleft : 0 ≤ ‖completedList L o d (l n) z‖ := norm_nonneg _
    have hscale : (squareWeight d : ℝ)*‖completedList L o d (l n) z‖ ≤ ‖z‖ := by
      calc
        _ ≤ (squareWeight d : ℝ)*((squareWeight d : ℝ)⁻¹*‖z‖) :=
          mul_le_mul_of_nonneg_left hl (squareWeight d).coe_nonneg
        _ = ‖z‖ := by rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt (squareWeight_pos d)),one_mul]
    have hs := pow_le_pow_left₀ (mul_nonneg (squareWeight d).coe_nonneg hleft) hscale 2
    simpa only [mul_pow,heq] using hs
  · intro i
    simpa only [hu] using hd i

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_compatible_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (K : ℝ≥0) (hF : ∀ i, F i ∈ VClass B h)
    (hLip : ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
      LipschitzWith K (fun s => ∑ i, ε i*F i s))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  apply compatible_detectors_false (sourceClasses B) c0Origin m M hm F (2*h+1) K _ hLip hδ hd
  intro i
  simpa only [sourceClasses_odd] using VClass_mono (Nat.le_succ h) (hF i)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem detection_split (a b : ℕ → ℝ) {δ : ℝ}
    (hd : ∀ i, δ ≤ |a i+b i|) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, δ/2 ≤ |a (φ i)|) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, δ/2 ≤ |b (φ i)|) := by
  have hh : ∀ i, δ/2 ≤ |a i| ∨ δ/2 ≤ |b i| := by
    intro i
    by_contra hn
    push Not at hn
    have h := (hd i).trans (abs_add_le (a i) (b i))
    linarith [hn.1,hn.2]
  have hf := Filter.frequently_or_distrib.mp (show ∀ᶠ i in atTop, δ/2 ≤ |a i| ∨ δ/2 ≤ |b i| from Filter.Eventually.of_forall hh).frequently
  rcases hf with hf | hf
  · exact Or.inl (extraction_of_frequently_atTop hf)
  · exact Or.inr (extraction_of_frequently_atTop hf)

namespace CylinderOperation
variable {I : Finset ℕ}

def remainder (op : CylinderOperation I) : CylinderOperation I := {op with isG := false}
@[simp] theorem remainder_scale (op : CylinderOperation I) : op.remainder.scale=op.scale := rfl
@[simp] theorem remainder_point (op : CylinderOperation I) : op.remainder.point=op.point := rfl
@[simp] theorem remainder_act (op : CylinderOperation I) (u : Cube I → ℝ) :
    op.remainder.act u = localR op.point op.scale u := rfl

theorem act_split (op : CylinderOperation I) (hG : op.isG=true) (u : Cube I → ℝ) :
    op.act u = u+op.remainder.act u := by
  rw [remainder_act]
  have he : op.act u = localG op.point op.scale u := by
    unfold act localOp
    rw [hG]
    rfl
  rw [he]
  ext x
  exact localG_eq op.point op.scale u x

theorem finite_scale_fiber (a : ℕ) : Finite {op : CylinderOperation I // op.scaleIndex=a} := by
  apply Finite.of_surjective
    (fun p : OperationGrid I a × Bool => (⟨⟨a,p.1,p.2⟩,rfl⟩ : {op : CylinderOperation I // op.scaleIndex=a}))
  rintro ⟨⟨a',c,g⟩,hh⟩
  change a'=a at hh
  subst a'
  exact ⟨(c,g),rfl⟩

theorem constant_or_small (op : ℕ → CylinderOperation I) :
    (∃ p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, op (φ i)=p) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => (op (φ i)).scale) atTop (nhds 0) ∧
      ∃ g : Bool, ∀ i, (op (φ i)).isG=g) := by
  rcases nat_constant_or_tendsto (fun i => (op i).scaleIndex) with ⟨a,ψ,hψ,ha⟩ | ha
  · let := finite_scale_fiber (I := I) a
    obtain ⟨p,η,hη,hp⟩ := finite_constant_subsequence
      (fun i => (⟨op (ψ i),ha i⟩ : {p : CylinderOperation I // p.scaleIndex=a}))
    exact Or.inl ⟨p.val,ψ ∘ η,hψ.comp hη,fun i => congrArg Subtype.val (hp i)⟩
  · obtain ⟨g,ψ,hψ,hg⟩ := finite_constant_subsequence (fun i => (op i).isG)
    exact Or.inr ⟨ψ,hψ,(dyadic_tendsto.comp ha).comp hψ.tendsto_atTop,g,hg⟩

end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def subrepresentation (r : GeneratedRepresentation B γ) (ops : List (CylinderOperation (B.coordinates γ)))
    (ho : ops.Sublist r.operations) : GeneratedRepresentation B γ where
  operations := ops
  ordered := r.ordered.sublist ho
  budget := lt_of_le_of_lt ((ho.map CylinderOperation.scale).sum_le_sum (by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    exact p.scale_pos.le)) r.budget

def sameScales (r : GeneratedRepresentation B γ) (ops : List (CylinderOperation (B.coordinates γ)))
    (hs : ops.map CylinderOperation.scale = r.operations.map CylinderOperation.scale) :
    GeneratedRepresentation B γ where
  operations := ops
  ordered := by
    apply (List.pairwise_map (R := fun a b : ℝ => b ≤ a)).mp
    rw [hs]
    exact List.pairwise_map.mpr r.ordered
  budget := by rw [hs]; exact r.budget

theorem length_le_of_prefix (r : GeneratedRepresentation B γ)
    (pre suf : List (CylinderOperation (B.coordinates γ))) (he : r.operations=pre++suf) {h : ℕ}
    (hh : r.operations.length ≤ h) : pre.length ≤ h := by
  rw [he,List.length_append] at hh
  omega

end GeneratedRepresentation

variable {Γ : Type*} {B : CylinderBases Γ}

theorem VClass_disjoint_false (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    (F : ℕ → C0Ball → ℝ) (h : ℕ) (hF : ∀ i, F i ∈ VClass B h)
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (F i)) (tsupport (F j))))
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|) : False := by
  refine VClass_compatible_false m M hm F h (4^h*B.L0+h*4^h*B.A) hF ?_ hδ hd
  intro n ε hε
  apply disjoint_supports_signed_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i : Fin n => F i) (4^h*B.L0+h*4^h*B.A) (fun i => VClass_lipschitz B h (hF i)) _ ε hε
  intro i j hij
  exact hdisj (show (i : ℕ) ≠ (j : ℕ) from fun he => hij (Fin.ext he))

theorem tail_escape_false (F : ℕ → C0Ball → ℝ) (m : ℕ → SourceSpace B)
    (h : ℕ) (hF : ∀ i, F i ∈ VClass B h) (M : ℝ) (hm : SignedBound m M)
    {δ cstar : ℝ} (hδ : 0 < δ) (hcstar : 0 < cstar)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m i)|)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hs : ∀ i s, s ∈ tsupport (F i) → cstar ≤ tau (N i) s.val) : False := by
  obtain ⟨H,φ,hφ,G,hG,hdG,hdis⟩ := tail_separation F m hF hδ hcstar hd N hN hs
  exact VClass_disjoint_false (m ∘ φ) M (hm.subsequence hφ.injective) G H hG hdis (half_pos hδ) hdG

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem small_remainders_false {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
    (r : ℕ → GeneratedRepresentation B γ) (ts : ℕ → List TailOperation) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ∀ i, (ts i).length ≤ h) (ha : ∀ i t, t ∈ ts i → t.scaleIndex ≤ h)
    (op : ℕ → CylinderOperation (B.coordinates γ))
    (hsmall : Tendsto (fun i => (op i).scale) atTop (nhds 0))
    (p : Cube (B.coordinates γ) → ℝ) (K : ℝ≥0) (hp : LipschitzWith K p)
    (suf : ℕ → List (CylinderOperation (B.coordinates γ)))
    (hlen : ∀ i, (suf i).length ≤ h)
    (horder : ∀ i t, t ∈ suf i → t.scale ≤ (op i).scale)
    (heq : ∀ i, (r i).cubeValue = applyOperations (suf i) ((op i).remainder.act p))
    (m : ℕ → SourceSpace B) (M : ℝ) (hm : SignedBound m M)
    {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin
      (fun s => (r i).value s*tailProduct (ts i) s) (m i)|) : False := by
  let a (i : ℕ) : ℝ := (h+1)*(op i).scale
  let b (i : ℕ) : ℝ := 2^h*K*(op i).scale
  have haPos (i : ℕ) : 0 < a i := by
    dsimp [a]; have := (op i).scale_pos; positivity
  have ha0 : Tendsto a atTop (nhds 0) := by simpa only [a,mul_zero] using hsmall.const_mul (h+1 : ℝ)
  have hb0 : Tendsto b atTop (nhds 0) := by simpa only [b,mul_zero] using hsmall.const_mul (2^h*(K : ℝ))
  have hsup (i : ℕ) (x : Cube (B.coordinates γ)) : |(r i).cubeValue x| ≤ b i := by
    rw [heq i]
    have hh := applyOperations_sup (suf i) (mul_nonneg (op i).scale_pos.le K.coe_nonneg)
      (fun x => localR_sup_lip (op i).point (op i).scale_pos p hp x) x
    rw [CylinderOperation.remainder_act]
    calc
      _ ≤ 2^(suf i).length*((op i).scale*K) := hh
      _ ≤ 2^h*((op i).scale*K) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (hlen i)) (mul_nonneg (op i).scale_pos.le K.coe_nonneg)
      _ = b i := by dsimp [b]; ring
  have hsupp (i : ℕ) (x : Cube (B.coordinates γ)) (hx : x ∈ tsupport (r i).cubeValue) :
      dist x (op i).point ≤ a i := by
    rw [heq i,CylinderOperation.remainder_act] at hx
    have hh := applyOperations_support_bound (suf i) (localR (op i).point (op i).scale p)
      (LipschitzWith.dist_left (op i).point) (fun x hx => localR_support_ball (op i).point (op i).scale_pos p hx) x hx
    have hs : ((suf i).map CylinderOperation.scale).sum ≤ (h : ℝ)*(op i).scale := by
      calc
        _ ≤ ((suf i).map (fun _ => (op i).scale)).sum := List.sum_le_sum (fun t ht => horder i t ht)
        _ = ((suf i).length : ℝ)*(op i).scale := by simp
        _ ≤ (h : ℝ)*(op i).scale := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen i) (op i).scale_pos.le
    dsimp [a]
    linarith
  obtain ⟨φ,hφ,F,hF,hdF,hLip⟩ := small_supports_compatible r ts h hr hj ht ha
    (fun i => (op i).point) a b haPos ha0 hb0 hsup hsupp m hδ hd
  exact VClass_compatible_false (m ∘ φ) M (hm.subsequence hφ.injective) F (h+1) _ hF hLip (half_pos hδ) hdF

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TailOperation
@[ext] theorem ext' {a b : TailOperation} (hs : a.scaleIndex=b.scaleIndex)
    (hn : a.tailIndex=b.tailIndex) (hg : a.isBasic=b.isBasic) : a=b := by
  cases a; cases b; simp_all

def remainder (t : TailOperation) : TailOperation := {t with isBasic := false}
@[simp] theorem remainder_scaleIndex (t : TailOperation) : t.remainder.scaleIndex=t.scaleIndex := rfl
@[simp] theorem remainder_tailIndex (t : TailOperation) : t.remainder.tailIndex=t.tailIndex := rfl
@[simp] theorem remainder_isBasic (t : TailOperation) : t.remainder.isBasic=false := rfl

theorem factor_split (t : TailOperation) (ht : t.isBasic=true) (s : C0Ball) :
    t.factor s = 1+t.remainder.factor s := by simp [factor,remainder,ht]

theorem constant_or_escape (t : ℕ → TailOperation) (h : ℕ) (ht : ∀ i, (t i).scaleIndex ≤ h) :
    (∃ p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, t (φ i)=p) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a g,
      (∀ i, (t (φ i)).scaleIndex=a) ∧ (∀ i, (t (φ i)).isBasic=g) ∧
      Tendsto (fun i => (t (φ i)).tailIndex) atTop atTop) := by
  obtain ⟨ag,ψ,hψ,hag⟩ := finite_constant_subsequence
    (fun i => ((⟨(t i).scaleIndex,Nat.lt_succ_of_le (ht i)⟩ : Fin (h+1)),(t i).isBasic))
  have ha (i : ℕ) : (t (ψ i)).scaleIndex=ag.1.val := congrArg (fun p : Fin (h+1) × Bool => p.1.val) (hag i)
  have hg (i : ℕ) : (t (ψ i)).isBasic=ag.2 := congrArg Prod.snd (hag i)
  rcases nat_constant_or_tendsto (fun i => (t (ψ i)).tailIndex) with ⟨N,η,hη,hN⟩ | hN
  · exact Or.inl ⟨⟨ag.1.val,N,ag.2⟩,ψ ∘ η,hψ.comp hη,fun i => ext' (ha _) (hN _) (hg _)⟩
  · exact Or.inr ⟨ψ,hψ,ag.1.val,ag.2,ha,hg,hN⟩
end TailOperation

@[simp] theorem tailProduct_append (pre post : List TailOperation) (s : C0Ball) :
    tailProduct (pre++post) s = tailProduct pre s*tailProduct post s := by
  simp only [tailProduct,List.map_append,List.prod_append]

theorem tailProduct_eq_zero (ts : List TailOperation) (t : TailOperation) (ht : t ∈ ts)
    (s : C0Ball) (hz : t.factor s=0) : tailProduct ts s=0 := by
  unfold tailProduct
  apply List.prod_eq_zero
  exact List.mem_map.mpr ⟨t,ht,hz⟩

theorem full_tail_support (f : C0Ball → ℝ) (ts : List TailOperation) (t : TailOperation)
    (ht : t ∈ ts) (hg : t.isBasic=false) :
    tsupport (fun s => f s*tailProduct ts s) ⊆ {s | dyadic t.scaleIndex ≤ tau (t.tailIndex+1) s.val} := by
  apply closure_minimal
  · intro s hs
    have hn : t.factor s ≠ 0 := by
      intro hz
      exact hs (by change f s*tailProduct ts s=0; rw [tailProduct_eq_zero ts t ht s hz,mul_zero])
    have hh := remainderTail_support (dyadic_pos t.scaleIndex) (t.tailIndex+1)
      (subset_tsupport _ (show tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1 ≠ 0 by
        simpa only [TailOperation.factor,hg,Bool.false_eq_true,↓reduceIte] using hn))
    exact hh
  · exact isClosed_le continuous_const ((tau_lipschitz _).continuous.comp continuous_subtype_val)

end
end C0Absorption

end OAI

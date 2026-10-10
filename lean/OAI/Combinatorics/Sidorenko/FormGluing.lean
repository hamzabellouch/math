import OAI.Combinatorics.Sidorenko.Lagrangian

namespace OAI

namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section UniformMaps
variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Finite U] [Finite W]

noncomputable def preimageFiberEquiv (f : U →ₗ[K] W) (P : W → Prop) :
    {x : U // P (f x)} ≃ Σ y : {y : W // P y}, {x : U // f x = y.val} where
  toFun x := ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun y := ⟨y.2.val, by simpa only [y.2.property] using y.1.property⟩
  left_inv _ := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
    cases hx
    rfl

 theorem surjective_linear_preimage_card (f : U →ₗ[K] W)
    (hf : Function.Surjective f) (P : W → Prop) :
    Nat.card {x : U // P (f x)} = Nat.card {y : W // P y} * Nat.card f.ker := by
  classical
  let : Fintype U := Fintype.ofFinite _
  let : Fintype W := Fintype.ofFinite _
  have hcard (y : W) : Nat.card {x : U // f x = y} = Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simpa [Fintype.card_subtype, LinearMap.mem_ker] using
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  rw [Nat.card_congr (preimageFiberEquiv f P), Nat.card_sigma]
  simp only [hcard, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]

 theorem surjective_linear_card (f : U →ₗ[K] W) (hf : Function.Surjective f) :
    Nat.card U = Nat.card W * Nat.card f.ker := by
  have h := surjective_linear_preimage_card f hf (fun _ => True)
  simpa using h

 theorem surjective_linear_probability (f : U →ₗ[K] W)
    (hf : Function.Surjective f) (P : W → Prop) :
    (Nat.card {x : U // P (f x)} : ℝ) / Nat.card U =
      (Nat.card {y : W // P y} : ℝ) / Nat.card W := by
  rw [surjective_linear_preimage_card f hf P, surjective_linear_card f hf]
  have hk : (Nat.card f.ker : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := f.ker)).ne'
  push_cast
  exact mul_div_mul_right _ _ hk

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weightedCombination (t : ι → K) : (ι → W) →ₗ[K] W :=
  ∑ i, t i • LinearMap.proj i

omit [Finite W] in
 theorem weightedCombination_surjective (t : ι → K) (ht : t ≠ 0) :
    Function.Surjective (weightedCombination (W := W) t) := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, t i ≠ 0 := by simpa [funext_iff] using ht
  intro w
  refine ⟨Pi.single i ((t i)⁻¹ • w), ?_⟩
  simp [weightedCombination, Pi.single_apply, hi]

end UniformMaps


section FiniteUnion
variable {T Ω : Type*} [Fintype T] [Finite Ω] [Nonempty Ω]

omit [Nonempty Ω] in
 theorem finite_union_card_bound (A : T → Ω → Prop) :
    Nat.card {x : Ω // ∃ t, A t x} ≤ ∑ t, Nat.card {x : Ω // A t x} := by
  let f : (Σ t : T, {x : Ω // A t x}) → {x : Ω // ∃ t, A t x} :=
    fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,t,ht⟩
    exact ⟨⟨t,⟨x,ht⟩⟩,rfl⟩
  exact (Nat.card_le_card_of_surjective f hf).trans_eq Nat.card_sigma

 theorem finite_union_probability_bound (A : T → Ω → Prop) (C : ℝ)
    (hA : ∀ t, (Nat.card {x : Ω // A t x} : ℝ) / Nat.card Ω ≤ C) :
    (Nat.card {x : Ω // ∃ t, A t x} : ℝ) / Nat.card Ω ≤ (Fintype.card T : ℝ)*C := by
  have hc : (0:ℝ) < Nat.card Ω := by exact_mod_cast Nat.card_pos (α := Ω)
  calc
    _ ≤ (∑ t, (Nat.card {x : Ω // A t x} : ℝ)) / Nat.card Ω := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact_mod_cast finite_union_card_bound A
    _ = ∑ t, (Nat.card {x : Ω // A t x} : ℝ) / Nat.card Ω := Finset.sum_div ..
    _ ≤ ∑ _t : T, C := Finset.sum_le_sum (fun t _ => hA t)
    _ = _ := by simp

end FiniteUnion

section GoodMinors
variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

def symmetricFormSubmodule : Submodule K (LinearMap.BilinForm K V) where
  carrier := {B | B.IsSymm}
  zero_mem' := ⟨fun _ _ => rfl⟩
  add_mem' := fun hB hC => hB.add hC
  smul_mem' := fun a _ hB => hB.smul a

noncomputable instance : AddCommGroup (SymForm K V) := by
  change AddCommGroup (symmetricFormSubmodule (K := K) (V := V))
  exact Submodule.addCommGroup (R := K) (M := LinearMap.BilinForm K V) (symmetricFormSubmodule (K := K) (V := V))
noncomputable instance : Module K (SymForm K V) := by
  change Module K (symmetricFormSubmodule (K := K) (V := V))
  exact Submodule.module (symmetricFormSubmodule (K := K) (V := V))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem symmetric_combination_nullity_bound (t : ι → K) (ht : t ≠ 0)
    (u : ℕ) (hu : u ≤ finrank K V) :
    (Nat.card {Q : ι → SymForm K V //
      u ≤ finrank K (weightedCombination t Q).val.ker} : ℝ) /
      Nat.card (ι → SymForm K V) ≤ 2^u / (Fintype.card K : ℝ)^((u+1).choose 2) := by
  rw [surjective_linear_probability (weightedCombination t)
    (weightedCombination_surjective t ht) (fun B : SymForm K V => u ≤ finrank K B.val.ker)]
  exact symmetric_nullity_probability_bound u hu


/-- The simultaneous bad-combination event, before invertibility
conditioning. The union is over every nonzero frequency, not only a fixed
one; its cardinal cost is explicitly q^s. -/
 theorem symmetric_bad_span_bound (u : ℕ) (hu : u ≤ finrank K V) :
    (Nat.card {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      u ≤ finrank K (weightedCombination t Q).val.ker} : ℝ) /
      Nat.card (ι → SymForm K V) ≤
      (Fintype.card K : ℝ)^(Fintype.card ι) *
        (2^u / (Fintype.card K : ℝ)^((u+1).choose 2)) := by
  classical
  let T := {t : ι → K // t ≠ 0}
  have heq : {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      u ≤ finrank K (weightedCombination t Q).val.ker} ≃
      {Q : ι → SymForm K V // ∃ t : T,
      u ≤ finrank K (weightedCombination t.val Q).val.ker} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun Q => by
      constructor
      · rintro ⟨t,ht,h⟩
        exact ⟨⟨t,ht⟩,h⟩
      · rintro ⟨t,h⟩
        exact ⟨t.val,t.property,h⟩)
  rw [Nat.card_congr heq]
  refine (finite_union_probability_bound
    (fun t : T => fun Q : ι → SymForm K V =>
      u ≤ finrank K (weightedCombination t.val Q).val.ker)
    _ (fun t => symmetric_combination_nullity_bound t.val t.property u hu)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hcard : Fintype.card T ≤ Fintype.card (ι → K) := Fintype.card_subtype_le _
  rw [Fintype.card_fun] at hcard
  exact_mod_cast hcard

 theorem symmetric_low_rank_span_bound (s : ℕ) (hs : s ≤ finrank K V) :
    (Nat.card {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      finrank K (weightedCombination t Q).val.range ≤ s} : ℝ) /
      Nat.card (ι → SymForm K V) ≤
      (Fintype.card K : ℝ)^(Fintype.card ι) *
        (2^(finrank K V-s) / (Fintype.card K : ℝ)^((finrank K V-s+1).choose 2)) := by
  have heq : {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      finrank K (weightedCombination t Q).val.range ≤ s} ≃
      {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      finrank K V-s ≤ finrank K (weightedCombination t Q).val.ker} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun Q => by
      apply exists_congr
      intro t
      change (t ≠ 0 ∧ finrank K (weightedCombination t Q).val.range ≤ s) ↔
        (t ≠ 0 ∧ finrank K V-s ≤ finrank K (weightedCombination t Q).val.ker)
      have h : finrank K (weightedCombination t Q).val.range +
          finrank K (weightedCombination t Q).val.ker = finrank K V :=
        (weightedCombination t Q).val.finrank_range_add_finrank_ker
      apply and_congr_right
      intro ht
      constructor
      · intro hr
        omega
      · intro hk
        omega)
  rw [Nat.card_congr heq]
  exact symmetric_bad_span_bound (finrank K V-s) (Nat.sub_le _ _)

end GoodMinors
end SidorenkoCounterexample


namespace SidorenkoCounterexample
section FormGluing
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup V] [Module K V]

/-- Symmetric forms descend through a linear map precisely when its kernel
is in the radical; the result is extended to the ambient codomain. -/
 theorem symmetric_form_descend (f : E →ₗ[K] V) (B : LinearMap.BilinForm K E)
    (hB : B.IsSymm) (hk : f.ker ≤ B.ker) :
    ∃ C : LinearMap.BilinForm K V, C.IsSymm ∧ C.compl₁₂ f f = B := by
  obtain ⟨p,hp⟩ := f.range.subtype.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr f.range.subtype_injective)
  let e := f.quotKerEquivRange
  let Q := LinearMap.IsRefl.liftQ₂ B f.ker hB.isRefl hk
  let g : V →ₗ[K] (E ⧸ f.ker) := e.symm.toLinearMap.comp p
  have hg (x : E) : g (f x) = f.ker.mkQ x := by
    apply e.injective
    change e (e.symm (p (f x))) = e (f.ker.mkQ x)
    rw [e.apply_symm_apply]
    have hp' := LinearMap.congr_fun hp (f.rangeRestrict x)
    exact hp'
  refine ⟨Q.compl₁₂ g g, ?_, ?_⟩
  · constructor
    intro x y
    change Q (g x) (g y) = Q (g y) (g x)
    generalize g x = a, g y = b
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction b using Submodule.Quotient.induction_on with
      | H b => exact hB.eq a b
  · apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q (g (f x)) (g (f y)) = B x y
    rw [hg,hg]
    rfl

 theorem symmetric_form_extend (U : Submodule K V) (B : LinearMap.BilinForm K U)
    (hB : B.IsSymm) :
    ∃ C : LinearMap.BilinForm K V, C.IsSymm ∧ C.compl₁₂ U.subtype U.subtype = B := by
  apply symmetric_form_descend U.subtype B hB
  rw [Submodule.ker_subtype]
  exact bot_le

/-- The cross block implementing gluing of forms on two subspaces. Its
restrictions to the common subspace agree with the prescribed forms. -/
def glueCross (U W : Submodule K V) (B : LinearMap.BilinForm K U)
    (C : LinearMap.BilinForm K W)
    (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W)) :
    U →ₗ[K] W →ₗ[K] K :=
  B.compl₂ ((Submodule.inclusion inf_le_left).comp q) +
  LinearMap.comp C ((Submodule.inclusion inf_le_right).comp p) -
  (B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left)).compl₁₂ p q

variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
variable (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W))

 theorem glueCross_left (hp : p.comp (Submodule.inclusion inf_le_left) = LinearMap.id)
    (s : ↥(U ⊓ W)) (w : W) :
    glueCross U W B C p q (Submodule.inclusion inf_le_left s) w =
      C (Submodule.inclusion inf_le_right s) w := by
  have hps := LinearMap.congr_fun hp s
  change p (Submodule.inclusion inf_le_left s) = s at hps
  change B (Submodule.inclusion inf_le_left s) (Submodule.inclusion inf_le_left (q w)) +
    C (Submodule.inclusion inf_le_right (p (Submodule.inclusion inf_le_left s))) w -
    B (Submodule.inclusion inf_le_left (p (Submodule.inclusion inf_le_left s)))
      (Submodule.inclusion inf_le_left (q w)) = _
  rw [hps]
  ring

 theorem glueCross_right (hq : q.comp (Submodule.inclusion inf_le_right) = LinearMap.id)
    (hBC : B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) =
      C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right))
    (u : U) (s : ↥(U ⊓ W)) :
    glueCross U W B C p q u (Submodule.inclusion inf_le_right s) =
      B u (Submodule.inclusion inf_le_left s) := by
  have hqs := LinearMap.congr_fun hq s
  change q (Submodule.inclusion inf_le_right s) = s at hqs
  have hc := LinearMap.congr_fun (LinearMap.congr_fun hBC (p u)) s
  change B (Submodule.inclusion inf_le_left (p u)) (Submodule.inclusion inf_le_left s) =
    C (Submodule.inclusion inf_le_right (p u)) (Submodule.inclusion inf_le_right s) at hc
  change B u (Submodule.inclusion inf_le_left (q (Submodule.inclusion inf_le_right s))) +
    C (Submodule.inclusion inf_le_right (p u)) (Submodule.inclusion inf_le_right s) -
    B (Submodule.inclusion inf_le_left (p u))
      (Submodule.inclusion inf_le_left (q (Submodule.inclusion inf_le_right s))) = _
  rw [hqs]
  rw [hc]
  ring



 theorem symmetric_form_glue (hB : B.IsSymm) (hC : C.IsSymm)
    (hBC : B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) =
      C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right)) :
    ∃ F : LinearMap.BilinForm K V, F.IsSymm ∧
      F.compl₁₂ U.subtype U.subtype = B ∧ F.compl₁₂ W.subtype W.subtype = C := by
  let i : ↥(U ⊓ W) →ₗ[K] U := Submodule.inclusion inf_le_left
  let j : ↥(U ⊓ W) →ₗ[K] W := Submodule.inclusion inf_le_right
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun u : U => u.val) h)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : W => w.val) h)
  obtain ⟨p,hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨q,hq⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let A := glueCross U W B C p q
  let fst := LinearMap.fst K U W
  let snd := LinearMap.snd K U W
  let D : LinearMap.BilinForm K (U × W) :=
    B.compl₁₂ fst fst + C.compl₁₂ snd snd +
    A.compl₁₂ fst snd + A.flip.compl₁₂ snd fst
  have hD (x y : U × W) : D x y = B x.1 y.1 + C x.2 y.2 + A x.1 y.2 + A y.1 x.2 := rfl
  have hDs : D.IsSymm := by
    constructor
    intro x y
    rw [hD,hD,hB.eq x.1 y.1,hC.eq x.2 y.2]
    ring
  let f : U × W →ₗ[K] V := U.subtype.comp fst + W.subtype.comp snd
  have hf (x : U × W) : f x = x.1.val + x.2.val := rfl
  have hk : f.ker ≤ D.ker := by
    intro x hx
    have hsum : x.1.val + x.2.val = 0 := hx
    have hxW : x.1.val ∈ W := by
      have hh : x.1.val = -x.2.val := eq_neg_of_add_eq_zero_left hsum
      rw [hh]
      exact W.neg_mem x.2.property
    let s : ↥(U ⊓ W) := ⟨x.1.val, x.1.property, hxW⟩
    have hxs : x = (i s, -j s) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact (eq_neg_of_add_eq_zero_right hsum)
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    change D x y = 0
    rw [hxs,hD]
    change B (i s) y.1 + C (-j s) y.2 + A (i s) y.2 + A y.1 (-j s) = 0
    simp only [map_neg, LinearMap.neg_apply]
    rw [glueCross_left U W B C p q hp,
      glueCross_right U W B C p q hq hBC, hB.eq]
    ring
  obtain ⟨F,hFs,hDF⟩ := symmetric_form_descend f D hDs hk
  refine ⟨F,hFs,?_,?_⟩
  · apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun (LinearMap.congr_fun hDF (u,0)) (v,0)
    change F (f (u,0)) (f (v,0)) = D (u,0) (v,0) at h
    simpa [hf,hD] using h
  · apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun (LinearMap.congr_fun hDF (0,u)) (0,v)
    change F (f (0,u)) (f (0,v)) = D (0,u) (0,v) at h
    simpa [hf,hD] using h

/-- Pointwise form of simultaneous extension, avoiding any implicit identification
of the two copies of the common subspace. -/
theorem symmetric_form_glue_pointwise (hB : B.IsSymm) (hC : C.IsSymm)
    (hc : ∀ (x y : V) (hxU : x ∈ U) (hxW : x ∈ W) (hyU : y ∈ U) (hyW : y ∈ W),
      B ⟨x,hxU⟩ ⟨y,hyU⟩ = C ⟨x,hxW⟩ ⟨y,hyW⟩) :
    ∃ F : LinearMap.BilinForm K V, F.IsSymm ∧
      F.compl₁₂ U.subtype U.subtype = B ∧ F.compl₁₂ W.subtype W.subtype = C := by
  apply symmetric_form_glue U W B C hB hC
  ext x y
  exact hc x y x.property.1 x.property.2 y.property.1 y.property.2

end FormGluing
section CyclicDifference
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]




theorem cyclic_difference_exists (A₀ A₁ A₂ : Submodule K V)
    (D₀ : LinearMap.BilinForm K ↥(A₁ ⊓ A₂))
    (D₁ : LinearMap.BilinForm K ↥(A₂ ⊓ A₀))
    (D₂ : LinearMap.BilinForm K ↥(A₀ ⊓ A₁))
    (hD₀ : D₀.IsSymm) (hD₁ : D₁.IsSymm) (hD₂ : D₂.IsSymm)
    (hc : ∀ (x y : V) (hx₀ : x ∈ A₀) (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
      (hy₀ : y ∈ A₀) (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂),
      D₀ ⟨x,hx₁,hx₂⟩ ⟨y,hy₁,hy₂⟩ + D₁ ⟨x,hx₂,hx₀⟩ ⟨y,hy₂,hy₀⟩ +
        D₂ ⟨x,hx₀,hx₁⟩ ⟨y,hy₀,hy₁⟩ = 0) :
    ∃ F G : LinearMap.BilinForm K V, F.IsSymm ∧ G.IsSymm ∧
      (F-G).compl₁₂ (A₁ ⊓ A₂).subtype (A₁ ⊓ A₂).subtype = D₀ ∧
      G.compl₁₂ (A₂ ⊓ A₀).subtype (A₂ ⊓ A₀).subtype = D₁ ∧
      (-F).compl₁₂ (A₀ ⊓ A₁).subtype (A₀ ⊓ A₁).subtype = D₂ := by
  let S := (A₁ ⊓ A₂) ⊓ (A₀ ⊓ A₁)
  let i : S →ₗ[K] ↥(A₁ ⊓ A₂) := Submodule.inclusion inf_le_left
  let j : S →ₗ[K] ↥(A₀ ⊓ A₁) := Submodule.inclusion inf_le_right
  let T : LinearMap.BilinForm K S := (-D₂).compl₁₂ j j
  have hT : T.IsSymm := by
    constructor
    intro x y
    change -(D₂ (j x) (j y)) = -(D₂ (j y) (j x))
    rw [hD₂.eq]
  have hi : i.ker = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y h
    exact Subtype.ext (congrArg (fun u : ↥(A₁ ⊓ A₂) => u.val) h))
  obtain ⟨H,hHs,hH⟩ := symmetric_form_descend i T hT (by rw [hi]; exact bot_le)
  have hHval (x y : V) (hx₀ : x ∈ A₀) (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
      (hy₀ : y ∈ A₀) (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂) :
      H ⟨x,hx₁,hx₂⟩ ⟨y,hy₁,hy₂⟩ = -D₂ ⟨x,hx₀,hx₁⟩ ⟨y,hy₀,hy₁⟩ :=
    LinearMap.congr_fun (LinearMap.congr_fun hH ⟨x,⟨hx₁,hx₂⟩,hx₀,hx₁⟩)
      ⟨y,⟨hy₁,hy₂⟩,hy₀,hy₁⟩
  have hneg : (-D₂).IsSymm := by
    constructor
    intro x y
    change -(D₂ x y) = -(D₂ y x)
    rw [hD₂.eq]
  obtain ⟨F,hFs,hF₀,hF₂⟩ := symmetric_form_glue_pointwise
    (A₁ ⊓ A₂) (A₀ ⊓ A₁) H (-D₂) hHs hneg (by
      intro x y hx hy hx' hy'
      exact hHval x y hy.1 hx.1 hx.2 hy'.1 hx'.1 hx'.2)
  have hsub : (H-D₀).IsSymm := by
    constructor
    intro x y
    change H x y - D₀ x y = H y x - D₀ y x
    rw [hHs.eq,hD₀.eq]
  obtain ⟨G,hGs,hG₀,hG₁⟩ := symmetric_form_glue_pointwise
    (A₁ ⊓ A₂) (A₂ ⊓ A₀) (H-D₀) D₁ hsub hD₁ (by
      intro x y hx hy hx' hy'
      change H ⟨x,hx⟩ ⟨y,hx'⟩ - D₀ ⟨x,hx⟩ ⟨y,hx'⟩ = D₁ ⟨x,hy⟩ ⟨y,hy'⟩
      rw [hHval x y hy.2 hx.1 hx.2 hy'.2 hx'.1 hx'.2]
      have h := hc x y hy.2 hx.1 hx.2 hy'.2 hx'.1 hx'.2
      linear_combination -h)
  refine ⟨F,G,hFs,hGs,?_,hG₁,?_⟩
  · ext x y
    have hf := LinearMap.congr_fun (LinearMap.congr_fun hF₀ x) y
    have hg := LinearMap.congr_fun (LinearMap.congr_fun hG₀ x) y
    change F x y = H x y at hf
    change G x y = H x y - D₀ x y at hg
    change F x y - G x y = D₀ x y
    rw [hf,hg]
    ring
  · ext x y
    have hf := LinearMap.congr_fun (LinearMap.congr_fun hF₂ x) y
    change F x y = -D₂ x y at hf
    change -(F x y) = D₂ x y
    rw [hf,neg_neg]

end CyclicDifference
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section PlantedDifference
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

noncomputable def symFormPull (f : V →ₗ[K] W) : SymForm K W →ₗ[K] SymForm K V where
  toFun B := ⟨B.val.compl₁₂ f f, by constructor; intro x y; exact B.property.eq (f x) (f y)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symFormPull_surjective (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Function.Surjective (symFormPull f) := by
  intro B
  obtain ⟨C,hCs,hC⟩ := symmetric_form_descend f B.val B.property
    (by rw [LinearMap.ker_eq_bot.mpr hf]; exact bot_le)
  exact ⟨⟨C,hCs⟩,Subtype.ext hC⟩

variable (A₀ A₁ A₂ : Submodule K V)
abbrev DifferenceTargets := SymForm K ↥(A₁ ⊓ A₂) ×
  (SymForm K ↥(A₂ ⊓ A₀) × SymForm K ↥(A₀ ⊓ A₁))
abbrev CommonSpace := ↥((A₀ ⊓ A₁) ⊓ A₂)

def commonInclusion₀ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₁ ⊓ A₂) :=
  Submodule.inclusion (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
def commonInclusion₁ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₂ ⊓ A₀) :=
  Submodule.inclusion (le_inf inf_le_right (inf_le_left.trans inf_le_left))
def commonInclusion₂ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₀ ⊓ A₁) :=
  Submodule.inclusion inf_le_left

noncomputable def cyclicDifferenceMap : (Fin 3 → SymForm K V) →ₗ[K]
    DifferenceTargets A₀ A₁ A₂ :=
  let p (i : Fin 3) : (Fin 3 → SymForm K V) →ₗ[K] SymForm K V := LinearMap.proj i
  ((symFormPull (A₁ ⊓ A₂).subtype).comp (p 1 - p 2)).prod
    (((symFormPull (A₂ ⊓ A₀).subtype).comp (p 2 - p 0)).prod
      ((symFormPull (A₀ ⊓ A₁).subtype).comp (p 0 - p 1)))

noncomputable def differenceConstraint : DifferenceTargets A₀ A₁ A₂ →ₗ[K]
    SymForm K (CommonSpace A₀ A₁ A₂) :=
  (symFormPull (commonInclusion₀ A₀ A₁ A₂)).comp (LinearMap.fst K _ _) +
  (symFormPull (commonInclusion₁ A₀ A₁ A₂)).comp
    ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _)) +
  (symFormPull (commonInclusion₂ A₀ A₁ A₂)).comp
    ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _))

theorem differenceConstraint_surjective :
    Function.Surjective (differenceConstraint A₀ A₁ A₂) := by
  intro B
  have hi : Function.Injective (commonInclusion₀ A₀ A₁ A₂) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥(A₁ ⊓ A₂) => z.val) h)
  obtain ⟨C,hC⟩ := symFormPull_surjective (commonInclusion₀ A₀ A₁ A₂) hi B
  refine ⟨(C,0,0), ?_⟩
  change symFormPull (commonInclusion₀ A₀ A₁ A₂) C +
    symFormPull (commonInclusion₁ A₀ A₁ A₂) 0 +
    symFormPull (commonInclusion₂ A₀ A₁ A₂) 0 = B
  simp [hC]

/-- The exact image, with all common-space constraints retained. -/
theorem cyclicDifference_range :
    (cyclicDifferenceMap A₀ A₁ A₂).range = (differenceConstraint A₀ A₁ A₂).ker := by
  apply le_antisymm
  · rintro D ⟨F,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    ext x y
    change (F 1).val x y - (F 2).val x y +
      ((F 2).val x y - (F 0).val x y) +
      ((F 0).val x y - (F 1).val x y) = 0
    ring
  · intro D hD
    have hcon := LinearMap.mem_ker.mp hD
    obtain ⟨F,G,hFs,hGs,hFG,hG,hF⟩ := cyclic_difference_exists A₀ A₁ A₂
      D.1.val D.2.1.val D.2.2.val D.1.property D.2.1.property D.2.2.property (by
        intro x y hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
        exact congrArg (fun B : SymForm K (CommonSpace A₀ A₁ A₂) =>
          B.val ⟨x,⟨hx₀,hx₁⟩,hx₂⟩ ⟨y,⟨hy₀,hy₁⟩,hy₂⟩) hcon)
    refine ⟨![0,⟨F,hFs⟩,⟨G,hGs⟩], ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact hFG
    · apply Prod.ext
      · apply Subtype.ext
        ext x y
        change G x y - 0 = D.2.1.val x y
        rw [sub_zero]
        exact LinearMap.congr_fun (LinearMap.congr_fun hG x) y
      · apply Subtype.ext
        ext x y
        change 0 - F x y = D.2.2.val x y
        rw [zero_sub]
        exact LinearMap.congr_fun (LinearMap.congr_fun hF x) y

end PlantedDifference
end SidorenkoCounterexample

namespace SidorenkoCounterexample
section ConstraintDensity
variable {K U W X : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [Finite U] [Finite W] [Finite X]

/-- Conditioning a uniform vector on a surjective linear constraint costs at
most the cardinality of the constraint space. This is a counting inequality,
not an independence assumption about the constrained entries. -/
theorem linear_constraint_probability_bound (f : U →ₗ[K] W) (c : W →ₗ[K] X)
    (hc : Function.Surjective c) (hfc : f.range = c.ker) (P : W → Prop) :
    (Nat.card {u : U // P (f u)} : ℝ) / Nat.card U ≤
      (Nat.card X : ℝ) * (Nat.card {w : W // P w} : ℝ) / Nat.card W := by
  have hprob := surjective_linear_probability f.rangeRestrict (by rintro ⟨w,u,rfl⟩; exact ⟨u,rfl⟩)
    (fun w : f.range => P w.val)
  have hinj : Function.Injective (fun w : {w : f.range // P w.val} =>
      (⟨w.val.val,w.property⟩ : {w : W // P w})) := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {w : W // P w} => z.val) h
  have hcard := Nat.card_le_card_of_injective _ hinj
  have htotal := surjective_linear_card c hc
  have hx : (Nat.card X : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := X)).ne'
  have hk : (Nat.card c.ker : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := c.ker)).ne'
  calc
    (Nat.card {u : U // P (f u)} : ℝ) / Nat.card U =
        (Nat.card {w : f.range // P w.val} : ℝ) / Nat.card f.range := hprob
    _ ≤ (Nat.card {w : W // P w} : ℝ) / Nat.card f.range :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = (Nat.card X : ℝ) * (Nat.card {w : W // P w} : ℝ) / Nat.card W := by
      rw [hfc,htotal]
      push_cast
      field_simp

end ConstraintDensity
section ProductDensity
variable {U W X : Type*} [Finite U] [Finite W] [Finite X]

def triplePredicateEquiv (P : U → Prop) (Q : W → Prop) (R : X → Prop) :
    {z : U × (W × X) // P z.1 ∧ Q z.2.1 ∧ R z.2.2} ≃
      {u : U // P u} × ({w : W // Q w} × {x : X // R x}) where
  toFun z := (⟨z.val.1,z.property.1⟩,⟨z.val.2.1,z.property.2.1⟩,⟨z.val.2.2,z.property.2.2⟩)
  invFun z := ⟨(z.1.val,z.2.1.val,z.2.2.val),z.1.property,z.2.1.property,z.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Finite U] [Finite W] [Finite X] in
theorem triple_predicate_probability (P : U → Prop) (Q : W → Prop) (R : X → Prop) :
    (Nat.card {z : U × (W × X) // P z.1 ∧ Q z.2.1 ∧ R z.2.2} : ℝ) /
      Nat.card (U × (W × X)) =
    ((Nat.card {u : U // P u} : ℝ) / Nat.card U) *
      ((Nat.card {w : W // Q w} : ℝ) / Nat.card W) *
      ((Nat.card {x : X // R x} : ℝ) / Nat.card X) := by
  rw [Nat.card_congr (triplePredicateEquiv P Q R)]
  simp only [Nat.card_prod, Nat.cast_mul]
  ring

end ProductDensity
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section OriginalDifferences
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (A₀ A₁ A₂ : Submodule K V)
abbrev OriginalForms := SymForm K A₀ × (SymForm K A₁ × SymForm K A₂)

noncomputable def ambientRestrictions : (Fin 3 → SymForm K V) →ₗ[K]
    OriginalForms A₀ A₁ A₂ :=
  let p (i : Fin 3) : (Fin 3 → SymForm K V) →ₗ[K] SymForm K V := LinearMap.proj i
  ((symFormPull A₀.subtype).comp (p 0)).prod
    (((symFormPull A₁.subtype).comp (p 1)).prod ((symFormPull A₂.subtype).comp (p 2)))

noncomputable def originalCyclicDifference : OriginalForms A₀ A₁ A₂ →ₗ[K]
    DifferenceTargets A₀ A₁ A₂ :=
  let p₀ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₀ := LinearMap.fst K _ _
  let p₁ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₁ :=
    (LinearMap.fst K _ _).comp (LinearMap.snd K _ _)
  let p₂ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₂ :=
    (LinearMap.snd K _ _).comp (LinearMap.snd K _ _)
  ((symFormPull (Submodule.inclusion inf_le_left : ↥(A₁ ⊓ A₂) →ₗ[K] A₁)).comp p₁ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₁ ⊓ A₂) →ₗ[K] A₂)).comp p₂).prod
  (((symFormPull (Submodule.inclusion inf_le_left : ↥(A₂ ⊓ A₀) →ₗ[K] A₂)).comp p₂ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₂ ⊓ A₀) →ₗ[K] A₀)).comp p₀).prod
   ((symFormPull (Submodule.inclusion inf_le_left : ↥(A₀ ⊓ A₁) →ₗ[K] A₀)).comp p₀ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₀ ⊓ A₁) →ₗ[K] A₁)).comp p₁))

theorem ambientRestrictions_surjective : Function.Surjective (ambientRestrictions A₀ A₁ A₂) := by
  intro B
  obtain ⟨F₀,h₀⟩ := symFormPull_surjective A₀.subtype A₀.subtype_injective B.1
  obtain ⟨F₁,h₁⟩ := symFormPull_surjective A₁.subtype A₁.subtype_injective B.2.1
  obtain ⟨F₂,h₂⟩ := symFormPull_surjective A₂.subtype A₂.subtype_injective B.2.2
  refine ⟨![F₀,F₁,F₂], ?_⟩
  change (symFormPull A₀.subtype F₀,symFormPull A₁.subtype F₁,symFormPull A₂.subtype F₂) = B
  rw [h₀,h₁,h₂]

theorem originalDifference_comp_restriction :
    (originalCyclicDifference A₀ A₁ A₂).comp (ambientRestrictions A₀ A₁ A₂) =
      cyclicDifferenceMap A₀ A₁ A₂ := by
  apply LinearMap.ext
  intro F
  apply Prod.ext
  · apply Subtype.ext
    ext x y
    rfl
  · apply Prod.ext
    · apply Subtype.ext
      ext x y
      rfl
    · apply Subtype.ext
      ext x y
      rfl

/-- The image statement for exactly the independent form spaces appearing in
the planted lift, NOT an assumption of independent difference matrices. -/
theorem originalCyclicDifference_range :
    (originalCyclicDifference A₀ A₁ A₂).range = (differenceConstraint A₀ A₁ A₂).ker := by
  have h : (cyclicDifferenceMap A₀ A₁ A₂).range =
      (originalCyclicDifference A₀ A₁ A₂).range := by
    rw [← originalDifference_comp_restriction, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (ambientRestrictions_surjective A₀ A₁ A₂), Submodule.map_top]
  exact h.symm.trans (cyclicDifference_range A₀ A₁ A₂)



theorem planted_nullity_probability_bound [Fintype K] [Finite V]
    (t₀ t₁ t₂ : ℕ) (h₀ : t₀ ≤ finrank K ↥(A₁ ⊓ A₂))
    (h₁ : t₁ ≤ finrank K ↥(A₂ ⊓ A₀)) (h₂ : t₂ ≤ finrank K ↥(A₀ ⊓ A₁)) :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have hc := linear_constraint_probability_bound
    (originalCyclicDifference A₀ A₁ A₂) (differenceConstraint A₀ A₁ A₂)
    (differenceConstraint_surjective A₀ A₁ A₂) (originalCyclicDifference_range A₀ A₁ A₂)
    (fun D => t₀ ≤ finrank K D.1.val.ker ∧ t₁ ≤ finrank K D.2.1.val.ker ∧
      t₂ ≤ finrank K D.2.2.val.ker)
  have hp := triple_predicate_probability
    (fun B : SymForm K ↥(A₁ ⊓ A₂) => t₀ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₂ ⊓ A₀) => t₁ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₀ ⊓ A₁) => t₂ ≤ finrank K B.val.ker)
  rw [mul_div_assoc, hp, symForm_card, Nat.cast_pow] at hc
  refine hc.trans ?_
  have hb₀ := symmetric_nullity_probability_bound (K := K) (V := ↥(A₁ ⊓ A₂)) t₀ h₀
  have hb₁ := symmetric_nullity_probability_bound (K := K) (V := ↥(A₂ ⊓ A₀)) t₁ h₁
  have hb₂ := symmetric_nullity_probability_bound (K := K) (V := ↥(A₀ ⊓ A₁)) t₂ h₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (mul_le_mul hb₀ hb₁ (by positivity) (by positivity)) hb₂
    (by positivity) (by positivity)

end OriginalDifferences
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualLiftCost
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
 theorem lift_pair_profile_probability_bound (t₀ t₁ t₂ : ℕ)
    (h₀ : t₀ ≤ finrank K ↥(A₁ ⊓ A₂)) (h₁ : t₁ ≤ finrank K ↥(A₂ ⊓ A₀))
    (h₂ : t₂ ≤ finrank K ↥(A₀ ⊓ A₁)) :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have he (F : OriginalForms A₀ A₁ A₂) :
      (finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)) ↔
      (t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker) := by
    change (_ ≤ finrank K ↥(formGraph A₁ F.2.1.val ⊓ formGraph A₂ F.2.2.val) ∧
      _ ≤ finrank K ↥(formGraph A₂ F.2.2.val ⊓ formGraph A₀ F.1.val) ∧
      _ ≤ finrank K ↥(formGraph A₀ F.1.val ⊓ formGraph A₁ F.2.1.val)) ↔ _
    rw [graph_pair_intersection_finrank,graph_pair_intersection_finrank,graph_pair_intersection_finrank]
    simp only [Nat.add_le_add_iff_left]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact planted_nullity_probability_bound A₀ A₁ A₂ t₀ t₁ t₂ h₀ h₁ h₂
end ActualLiftCost
end SidorenkoCounterexample

end OAI

import OAI.Algebra.AffineCancellation.Kernel
import OAI.Algebra.AffineCancellation.GradedLND
import OAI.Algebra.AffineCancellation.QuotientGrading
import OAI.Algebra.AffineCancellation.QuotientDerivation
import OAI.Algebra.AffineCancellation.HighestWeight
import OAI.Algebra.AffineCancellation.Determinant

namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

def δP : Derivation ℂ Poly Poly := MvPolynomial.mkDerivation ℂ ![0,0,X 0,X 1,0]
def ηP : Derivation ℂ Poly Poly := MvPolynomial.mkDerivation ℂ ![X 2,X 3,0,0,0]

lemma δP_relation : δP relation = 0 := by
  simp [δP, relation, Derivation.leibniz, smul_eq_mul]
  ring
lemma ηP_relation : ηP relation = 0 := by
  simp [ηP, relation, Derivation.leibniz, smul_eq_mul]
  ring

def δ : Derivation ℂ T T := QuotientDerivation.derivation _ δP
  (QuotientDerivation.span_singleton_stable δP (by rw [δP_relation]; exact Ideal.zero_mem _))
def η : Derivation ℂ T T := QuotientDerivation.derivation _ ηP
  (QuotientDerivation.span_singleton_stable ηP (by rw [ηP_relation]; exact Ideal.zero_mem _))
def Euler : Derivation ℂ T T := ⁅δ,η⁆

@[simp] lemma δ_π (r : Poly) : δ (π r) = π (δP r) := rfl
@[simp] lemma η_π (r : Poly) : η (π r) = π (ηP r) := rfl
@[simp] lemma δ_a : δ a = 0 := by simp [a, δP]
@[simp] lemma δ_d : δ d = 0 := by simp [d, δP]
@[simp] lemma δ_b : δ b = a := by simp [a, b, δP]
@[simp] lemma δ_c : δ c = d := by simp [d, c, δP]
@[simp] lemma δ_u : δ u = 0 := by simp [u, δP]
@[simp] lemma η_a : η a = b := by simp [a, b, ηP]
@[simp] lemma η_d : η d = c := by simp [d, c, ηP]
@[simp] lemma η_b : η b = 0 := by simp [b, ηP]
@[simp] lemma η_c : η c = 0 := by simp [c, ηP]
@[simp] lemma η_u : η u = 0 := by simp [u, ηP]
@[simp] lemma Euler_a : Euler a = a := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_d : Euler d = d := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_b : Euler b = -b := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_c : Euler c = -c := by simp [Euler, Derivation.commutator_apply]
@[simp] lemma Euler_u : Euler u = 0 := by simp [Euler, Derivation.commutator_apply]

lemma derivation_ext {D₁ D₂ : Derivation ℂ T T}
    (hX : ∀ i : Fin 5, D₁ (π (X i)) = D₂ (π (X i))) : D₁ = D₂ := by
  apply Derivation.ext
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {relation}) r
  change D₁ (π r) = D₂ (π r)
  induction r using MvPolynomial.induction_on with
  | C z => simp [π]
  | add r s hr hs => simp only [map_add, hr, hs]
  | mul_X r i hr => simp only [map_mul, Derivation.leibniz, hr, hX]

lemma η_locallyNilpotent : LND.LocallyNilpotent η := by
  apply QuotientDerivation.locallyNilpotent
  apply LND.mvPolynomial_locallyNilpotent
  intro i
  refine ⟨2, ?_⟩
  fin_cases i <;> simp [Function.iterate_succ_apply', ηP]

lemma Euler_η (r : T) : Euler (η r) = η (Euler r) - (2 : ℂ) • η r := by
  have h : ⁅Euler,η⁆ = (-2 : ℂ) • η := by
    apply derivation_ext
    intro i
    fin_cases i <;>
      simp [Euler, Derivation.commutator_apply, δ_π, η_π, δP, ηP, Derivation.smul_apply] <;>
      module
  have hr := DFunLike.congr_fun h r
  simp only [Derivation.commutator_apply, Derivation.smul_apply] at hr
  rw [neg_smul] at hr
  linear_combination hr

/-- Exact infinitesimal formulation of a fixed fiber-weight shift. -/
def FiberShift (E : Derivation ℂ T T) (e : ℤ) : Prop :=
  ∀ r, Euler (E r) - E (Euler r) = (e : ℂ) • E r

lemma fixed_coefficients_contradiction (E : Derivation ℂ T T)
    (hE : E ≠ 0) (hln : LND.LocallyNilpotent E) (e : ℤ) (he : e ≤ 0)
    (hshift : FiberShift E e) (ha : E a = 0) (hd : E d = 0) (hu : E u = 0) : False := by
  let h := c * E b - b * E c
  have hrel : a * E c = d * E b := by
    have hh := congrArg E determinant
    simp only [map_sub, Derivation.leibniz, ha, hd, smul_eq_mul, mul_zero,
      add_zero, zero_add, Derivation.map_one_eq_zero] at hh
    linear_combination hh
  have hb : E b = h*a := by dsimp [h]; linear_combination -(E b) * determinant + b * hrel
  have hc : E c = h*d := by dsimp [h]; linear_combination -(E c) * determinant + c * hrel
  have hder : E = h • δ := by
    apply derivation_ext
    intro i
    fin_cases i
    · change E a = h * δ a; simp only [ha, δ_a, mul_zero]
    · change E d = h * δ d; simp only [hd, δ_d, mul_zero]
    · change E b = h * δ b; simpa only [δ_b] using hb
    · change E c = h * δ c; simpa only [δ_c] using hc
    · change E u = h * δ u; simp only [hu, δ_u, mul_zero]
  have hn : h ≠ 0 := by
    intro hh
    apply hE
    rw [hder, hh]
    apply Derivation.ext
    intro r
    change (0:T) * δ r = 0
    exact zero_mul _
  have hfix : δ h = 0 := by
    have hh : E h = 0 := LND.fixed_of_dvd E hln (by
      rw [hder, Derivation.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _)
    rw [hder, Derivation.smul_apply, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left hn
  have hweight : Euler h = ((e-2 : ℤ) : ℂ) • h := by
    have hb' := hshift b
    have hc' := hshift c
    simp only [Euler_b, Euler_c, map_neg] at hb' hc'
    dsimp [h]
    simp only [map_sub, Derivation.leibniz, Euler_b, Euler_c, smul_eq_mul]
    simp only [Int.cast_smul_eq_zsmul, zsmul_eq_mul] at hb' hc' ⊢
    push_cast
    linear_combination c * hb' - b * hc'
  exact hn (SL2.no_negative_highest δ.toLinearMap η.toLinearMap Euler.toLinearMap
    (fun r => rfl) Euler_η h (e-2) (by omega) hfix hweight (η_locallyNilpotent h))

end ComplexCancellation.Determinant

namespace ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def auxWeight : Fin 5 → ℤ := ![0,3,-3,0,2]
abbrev auxPoly : ℤ → Submodule ℂ Poly := weightedHomogeneousSubmodule ℂ auxWeight
abbrev aux : ℤ → Submodule ℂ T := QuotientGrading.pieces auxPoly π

lemma relation_aux : relation ∈ auxPoly 0 := by
  have h1 := (isWeightedHomogeneous_X (R := ℂ) auxWeight 0).mul
    (isWeightedHomogeneous_X (R := ℂ) auxWeight 3)
  have h2 := (isWeightedHomogeneous_X (R := ℂ) auxWeight 2).mul
    (isWeightedHomogeneous_X (R := ℂ) auxWeight 1)
  have h1' : IsWeightedHomogeneous auxWeight (X 0 * X 3 : Poly) 0 := by
    simpa [auxWeight] using h1
  have h2' : IsWeightedHomogeneous auxWeight (X 2 * X 1 : Poly) 0 := by
    simpa [auxWeight] using h2
  exact (h1'.sub h2').sub (isWeightedHomogeneous_one ℂ auxWeight)

lemma aux_ker : (RingHom.ker π).IsHomogeneous auxPoly := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {relation}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  have hr' : r = relation := Set.mem_singleton_iff.mp hr
  subst r
  exact ⟨0, relation_aux⟩

instance auxGrading : GradedAlgebra aux :=
  QuotientGrading.grading auxPoly π (Ideal.Quotient.mkₐ_surjective _ _) aux_ker

lemma aux_X (i : Fin 5) : π (X i) ∈ aux (auxWeight i) :=
  ⟨X i, isWeightedHomogeneous_X (R := ℂ) auxWeight i, rfl⟩
lemma aux_a : a ∈ aux 0 := aux_X 0
lemma aux_d : d ∈ aux 3 := aux_X 1
lemma aux_b : b ∈ aux (-3) := aux_X 2
lemma aux_c : c ∈ aux 0 := aux_X 3
lemma aux_u : u ∈ aux 2 := aux_X 4
lemma aux_N : d ^ 2 + a ^ 2 * u ^ 3 ∈ aux 6 := by
  have hd := SetLike.pow_mem_graded 2 aux_d
  have ha := SetLike.pow_mem_graded 2 aux_a
  have hu := SetLike.pow_mem_graded 3 aux_u
  have hi := SetLike.mul_mem_graded ha hu
  norm_num at hd hi
  exact Submodule.add_mem _ hd hi
lemma aux_a3b : a ^ 3 * b ∈ aux (-3) := by
  have ha := SetLike.pow_mem_graded 3 aux_a
  have hi := SetLike.mul_mem_graded ha aux_b
  norm_num at hi
  exact hi

lemma Euler_aux {r : T} {i : ℤ} (hr : r ∈ aux i) : Euler r ∈ aux i := by
  have he : Euler = GradedLND.component aux Euler 0 := by
    apply derivation_ext
    intro j
    rw [GradedLND.component_of_mem aux Euler 0 (aux_X j), add_zero]
    apply (GradedLND.proj_of_mem aux _).symm
    fin_cases j
    · change Euler a ∈ aux 0
      simpa only [Euler_a] using aux_a
    · change Euler d ∈ aux 3
      simpa only [Euler_d] using aux_d
    · change Euler b ∈ aux (-3)
      simpa only [Euler_b] using Submodule.neg_mem (aux (-3)) aux_b
    · change Euler c ∈ aux 0
      simpa only [Euler_c] using Submodule.neg_mem (aux 0) aux_c
    · change Euler u ∈ aux 2
      simpa only [Euler_u] using Submodule.zero_mem (aux 2)
  rw [he]
  simpa only [add_zero] using GradedLND.component_homogeneous aux Euler 0 hr

lemma Euler_proj (r : T) (i : ℤ) :
    Euler (GradedLND.proj aux i r) = GradedLND.proj aux i (Euler r) := by
  induction r using DirectSum.Decomposition.inductionOn aux with
  | zero => simp
  | @homogeneous j r =>
    by_cases hji : j = i
    · subst j
      rw [GradedLND.proj_of_mem aux r.2, GradedLND.proj_of_mem aux (Euler_aux r.2)]
    · rw [GradedLND.proj_of_mem_ne aux r.2 hji,
        GradedLND.proj_of_mem_ne aux (Euler_aux r.2) hji, map_zero]
  | add r s hr hs => simp only [map_add, hr, hs]

lemma component_fiberShift {E : Derivation ℂ T T} {e : ℤ} (hE : FiberShift E e)
    (j : ℤ) : FiberShift (GradedLND.component aux E j) e := by
  intro r
  induction r using DirectSum.Decomposition.inductionOn aux with
  | zero => simp
  | @homogeneous i r =>
    rw [GradedLND.component_of_mem aux E j r.2,
      GradedLND.component_of_mem aux E j (Euler_aux r.2), Euler_proj,
      ← map_sub, hE, map_smul]
  | add r s hr hs => simp only [map_add, smul_add]; linear_combination hr + hs

lemma nonzero_base_X (i : Fin 4) : baseMap (X i) ≠ 0 := by
  intro h
  exact X_ne_zero i (baseMap_injective (h.trans (map_zero _).symm))
lemma a_ne_zero : a ≠ 0 := by simpa [baseMap, baseValues] using nonzero_base_X 1
lemma d_ne_zero : d ≠ 0 := by simpa [baseMap, baseValues] using nonzero_base_X 2
lemma u_ne_zero : u ≠ 0 := by simpa [baseMap, baseValues] using nonzero_base_X 0
lemma N_ne_zero : d ^ 2 + a ^ 2 * u ^ 3 ≠ 0 := by
  intro h
  have he : baseMap (X 2 ^ 2 + X 1 ^ 2 * X 0 ^ 3) = 0 := by
    simpa [baseMap, baseValues] using h
  have hp : (X 2 ^ 2 + X 1 ^ 2 * X 0 ^ 3 : Base) = 0 :=
    baseMap_injective (he.trans (map_zero _).symm)
  have hz := congrArg (MvPolynomial.eval (fun i : Fin 4 => if i = 2 then (1 : ℂ) else 0)) hp
  simp at hz

lemma nonsquare_u (z : K) : z ^ 2 ≠ -(embedding u) ^ 3 := by
  have he : embedding u = RatFunc.X := by
    change embedding (π (X 4)) = _
    rw [embedding_π]
    simp only [eval, aeval_X]
    change baseEmbedding (X 0) = _
    exact baseEmbedding_X_zero
  rw [he]
  exact Rigidity.ratFunc_X_cube_nonsquare z

/-- Rigidity for the determinant algebra with its fiber Euler operator. -/
theorem rigidity (E : Derivation ℂ T T) (hln : LND.LocallyNilpotent E)
    (e : ℤ) (he : e ≤ 0) (hshift : FiberShift E e) (hv : E (E v) = 0) : E = 0 := by
  by_contra hE
  obtain ⟨j, hj, hbound, htopln⟩ := GradedLND.highest aux E hE hln
  let E' := GradedLND.component aux E j
  have hN : E' (E' (d ^ 2 + a ^ 2 * u ^ 3)) = 0 := by
    have ht := (GradedLND.iterate_top aux hbound aux_N 2).2
    have hl := (GradedLND.iterate_top aux hbound aux_a3b 2).1
    have hlow : GradedLND.proj aux (6+2*j) (E (E (a^3*b))) = 0 := by
      apply GradedLND.proj_filtration aux hl
      omega
    have heq : E (E (d ^ 2 + a ^ 2 * u ^ 3)) = E (E (a^3*b)) := by
      dsimp [v] at hv
      simp only [map_sub, map_add] at hv ⊢
      linear_combination -hv
    change GradedLND.proj aux (6+2*j) (E (E (d^2+a^2*u^3))) = E' (E' _) at ht
    rw [heq, hlow] at ht
    exact ht.symm
  obtain ⟨ha, hd, hu⟩ := LND.fixed_of_square_cube E' htopln embedding embedding_injective
    a_ne_zero d_ne_zero u_ne_zero N_ne_zero hN nonsquare_u
  exact fixed_coefficients_contradiction E' hj htopln e he (component_fiberShift hshift j) ha hd hu

end ComplexCancellation.Determinant

end

end OAI

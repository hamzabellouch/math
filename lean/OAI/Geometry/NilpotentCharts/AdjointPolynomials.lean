import Mathlib
import OAI.Geometry.NilpotentCharts.CentralAxes
import OAI.Geometry.NilpotentCharts.LinearLattices
import OAI.Geometry.NilpotentCharts.Polynomials
import OAI.Geometry.NilpotentCharts.SmoothCalculus

namespace OAI

/-! Polynomial one-parameter adjoint actions and triangular infinitesimal matrices. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawNilpotentPolynomial
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

 

theorem oneParameter_eq_exp (f : ℝ → A) (hf0 : f 0 = 1)
    (hadd : ∀ t u, f (t+u) = f t * f u) (B : A) (hd : HasDerivAt f B 0) :
    ∀ t, f t = NormedSpace.exp (t • B) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hdf (t : ℝ) : HasDerivAt f (f t * B) t := by
    have h := (hd.const_mul (f t)).scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    simp only [one_smul] at h
    have he : ((fun y => f t * f y) ∘ fun x => id x - t) = f := by
      funext x
      exact (hadd t (x-t)).symm.trans (congrArg f (by ring))
    rw [he] at h
    exact h
  have hzero (t : ℝ) : HasDerivAt (fun u => f u * NormedSpace.exp (u • (-B))) 0 t := by
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-B)))
        ((-B) * NormedSpace.exp (t • (-B))) t := hasDerivAt_exp_smul_const' (-B) t
    convert (hdf t).mul he using 1
    first | rfl | simp only [neg_mul,mul_neg,mul_assoc,add_neg_cancel]
  have hconst (t : ℝ) : f t * NormedSpace.exp (t • (-B)) = 1 := by
    have he := is_const_of_deriv_eq_zero (fun x => (hzero x).differentiableAt)
      (fun x => (hzero x).deriv) t 0
    simpa only [zero_smul,NormedSpace.exp_zero,hf0,mul_one] using he
  intro t
  have he := congrArg (fun x => x * NormedSpace.exp (t • B)) (hconst t)
  rw [mul_assoc,smul_neg,← NormedSpace.exp_add_of_commute ((Commute.refl (t • B)).neg_left)] at he
  simpa only [smul_neg,neg_add_cancel,NormedSpace.exp_zero,mul_one,one_mul] using he

omit [CompleteSpace A] in
lemma exp_nilpotent (B : A) {s : ℕ} (hs : B^s = 0) (t : ℝ) :
    NormedSpace.exp (t • B) = ∑ i ∈ Finset.range s, ((Nat.factorial i : ℝ)⁻¹ * t^i) • B^i := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  rw [tsum_eq_sum (s := Finset.range s)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [smul_pow,smul_smul]
  · intro i hi
    have hsi : s ≤ i := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hi)
    have hz : B^i = 0 := pow_eq_zero_of_le hsi hs
    simp only [smul_pow,hz,smul_zero]

theorem oneParameter_polynomial (f : ℝ → A) (hf0 : f 0 = 1)
    (hadd : ∀ t u, f (t+u) = f t * f u) (B : A) (hd : HasDerivAt f B 0)
    {s : ℕ} (hs : B^s = 0) (t : ℝ) :
    f t = ∑ i ∈ Finset.range s, ((Nat.factorial i : ℝ)⁻¹ * t^i) • B^i := by
  rw [oneParameter_eq_exp f hf0 hadd B hd,exp_nilpotent B hs]

 

omit [CompleteSpace A] in
lemma generator_nilpotent (f : ℝ → A) (hf0 : f 0 = 1) (B : A)
    (hd : HasDerivAt f B 0) (s : ℕ) (hn : ∀ t, (f t - 1)^s = 0) : B^s = 0 := by
  have hl := hd.tendsto_slope_zero.pow s
  simp only [zero_add,hf0,smul_pow,hn,smul_zero] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

theorem unipotent_oneParameter_polynomial (f : ℝ → A) (hf0 : f 0 = 1)
    (hadd : ∀ t u, f (t+u) = f t * f u) (B : A) (hd : HasDerivAt f B 0)
    (s : ℕ) (hn : ∀ t, (f t - 1)^s = 0) (t : ℝ) :
    f t = ∑ i ∈ Finset.range s, ((Nat.factorial i : ℝ)⁻¹ * t^i) • B^i :=
  oneParameter_polynomial f hf0 hadd B hd (generator_nilpotent f hf0 B hd s hn) t

end RawNilpotentPolynomial

namespace RawLieAdjoint
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

omit [FiniteDimensional ℝ E₀] [LieGroup I₀ ∞ G] [T2Space G] in
@[simp] lemma adjoint_one : adjoint (E₀ := E₀) (1 : G) = 1 := by
  change mfderiv I₀ I₀ (MulAut.conj (1 : G) : G → G) 1 = _
  rw [show (MulAut.conj (1 : G) : G → G) = id by ext x; simp]
  exact mfderiv_id

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma adjoint_mul (g h : G) : adjoint (E₀ := E₀) (g*h) = adjoint (E₀ := E₀) g * adjoint (E₀ := E₀) h := by
  have H := derivative_comp_one (E₀ := E₀) (map_one (MulAut.conj h))
    ((conjugation_smooth (E₀ := E₀) h).mdifferentiableAt one_ne_zero)
    ((conjugation_smooth (E₀ := E₀) g).mdifferentiableAt one_ne_zero)
  have he : (MulAut.conj g : G → G) ∘ MulAut.conj h = MulAut.conj (g*h) := by
    ext x
    simp only [Function.comp_apply,MulAut.conj_apply,mul_inv_rev,mul_assoc]
  rw [he] at H
  exact H

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma adjoint_sub_one_nilpotent {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (g : G) :
    (adjoint (E₀ := E₀) g - 1)^s = 0 := by
  have H := nilpotent_mixed_derivative (E₀ := E₀) hstop (List.replicate s g) (List.length_replicate ..)
  simp only [List.map_replicate,List.prod_replicate] at H
  have he : adjoint (E₀ := E₀) g - 1 = - derivative (E₀ := E₀) (commMap g) 1 := by
    have h := commMap_add_adjoint (E₀ := E₀) g
    change derivative (E₀ := E₀) (commMap g) 1 + adjoint (E₀ := E₀) g = 1 at h
    apply eq_neg_iff_add_eq_zero.mpr
    rw [sub_add_eq_add_sub,add_comm (adjoint (E₀ := E₀) g),h,sub_self]
  rw [he,neg_pow,H,mul_zero]

lemma adjoint_curve_contDiff (v : GroupLieAlgebra I₀ G) :
    ContDiff ℝ ∞ (fun t => adjoint (E₀ := E₀) (RawLieIntegration.curve v t)) := by
  apply RawParameterDerivative.contDiff_parameter_derivative
    (f := fun t g => RawLieIntegration.curve v t * g * (RawLieIntegration.curve v t)⁻¹)
    (p := (1 : G))
  · exact (((RawLieIntegration.curve_contMDiff v).comp contMDiff_fst).mul
      contMDiff_snd).mul (((RawLieIntegration.curve_contMDiff v).comp contMDiff_fst).inv)
  · intro t
    simp only [mul_one,mul_inv_cancel]

 

theorem adjoint_curve_polynomial {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (v : GroupLieAlgebra I₀ G) :
    ∃ B : E₀ →L[ℝ] E₀, B^s = 0 ∧ ∀ t : ℝ,
      adjoint (E₀ := E₀) (RawLieIntegration.curve v t) =
        ∑ i ∈ Finset.range s, ((Nat.factorial i : ℝ)⁻¹ * t^i) • B^i := by
  let f : ℝ → E₀ →L[ℝ] E₀ := fun t => adjoint (E₀ := E₀) (RawLieIntegration.curve v t)
  have hf : HasDerivAt f (deriv f 0) 0 :=
    ((adjoint_curve_contDiff v).differentiable (by simp) 0).hasDerivAt
  have h0 : f 0 = 1 := by simp only [f,RawLieIntegration.curve_zero,adjoint_one]
  have hp : ∀ t u, f (t+u) = f t * f u := by
    intro t u
    simp only [f,RawLieIntegration.curve_add,adjoint_mul]
  have hn : ∀ t, (f t - 1)^s = 0 := fun t => adjoint_sub_one_nilpotent hstop _
  exact ⟨deriv f 0,RawNilpotentPolynomial.generator_nilpotent f h0 _ hf s hn,
    RawNilpotentPolynomial.unipotent_oneParameter_polynomial f h0 hp _ hf s hn⟩

end RawLieAdjoint

namespace RawLieAdjoint
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma adjoint_contMDiff : ContMDiff I₀ 𝓘(ℝ,E₀ →L[ℝ] E₀) ∞ (adjoint (G := G) (E₀ := E₀)) := by
  apply RawParameterDerivativeGeneral.contMDiff_parameter_derivative
    (f := fun g h : G => g*h*g⁻¹) (p := (1 : G))
  · exact (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv
  · intro g; simp

def infinitesimal : E₀ →L[ℝ] (E₀ →L[ℝ] E₀) :=
  mfderiv I₀ 𝓘(ℝ,E₀ →L[ℝ] E₀) (adjoint (G := G) (E₀ := E₀)) 1

lemma infinitesimal_hasDerivAt (v : GroupLieAlgebra I₀ G) :
    HasDerivAt (fun t => adjoint (E₀ := E₀) (RawLieIntegration.curve v t))
      (infinitesimal (G := G) (E₀ := E₀) v) 0 := by
  have hd : HasMFDerivAt I₀ 𝓘(ℝ,E₀ →L[ℝ] E₀) (adjoint (E₀ := E₀))
      (RawLieIntegration.curve v 0) (infinitesimal (G := G) (E₀ := E₀)) := by
    rw [RawLieIntegration.curve_zero]
    exact (adjoint_contMDiff.mdifferentiable (by simp) 1).hasMFDerivAt
  have H := hd.comp 0 (RawLieIntegration.curve_derivative_zero v)
  have he : (infinitesimal (G := G) (E₀ := E₀)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (infinitesimal (G := G) (E₀ := E₀) v) := by
    apply ContinuousLinearMap.ext
    intro t
    change infinitesimal (G := G) (E₀ := E₀) (t • v) =
      t • infinitesimal (G := G) (E₀ := E₀) v
    exact map_smul (infinitesimal (G := G) (E₀ := E₀)) t v
  have hfd : HasFDerivAt
      (fun t => adjoint (E₀ := E₀) (RawLieIntegration.curve v t))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (infinitesimal (G := G) (E₀ := E₀) v)) 0 :=
    (H.congr_mfderiv he).hasFDerivAt
  simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul]
    using hfd.hasDerivAt

lemma adjoint_curve_self (v : GroupLieAlgebra I₀ G) (t : ℝ) :
    adjoint (E₀ := E₀) (RawLieIntegration.curve v t) v = v := by
  apply RawLieIntegration.curve_injective
  funext u
  have H := RawLieIntegration.curve_hom (MulAut.conj (RawLieIntegration.curve v t)).toMonoidHom
    ((conjugation_smooth (E₀ := E₀) (RawLieIntegration.curve v t)).mdifferentiable one_ne_zero) v u
  apply H.symm.trans
  change RawLieIntegration.curve v t * RawLieIntegration.curve v u *
    (RawLieIntegration.curve v t)⁻¹ = RawLieIntegration.curve v u
  rw [← RawLieIntegration.curve_neg,← RawLieIntegration.curve_add,
    ← RawLieIntegration.curve_add,show t+u+ -t = u by ring]

lemma infinitesimal_self (v : E₀) : infinitesimal (G := G) (E₀ := E₀) v v = 0 := by
  have H := (infinitesimal_hasDerivAt (G := G) v).clm_apply (hasDerivAt_const (0 : ℝ) v)
  have he : (fun t : ℝ => adjoint (E₀ := E₀) (RawLieIntegration.curve v t) v) = fun _ => v :=
    funext (adjoint_curve_self (G := G) (E₀ := E₀) v)
  rw [he] at H
  simpa only [map_zero,add_zero] using H.unique (hasDerivAt_const (0 : ℝ) v)

 

lemma infinitesimal_antisymm (v w : E₀) :
    infinitesimal (G := G) (E₀ := E₀) v w = - infinitesimal (G := G) (E₀ := E₀) w v := by
  have H := infinitesimal_self (G := G) (v+w)
  simp only [map_add,add_apply,infinitesimal_self,zero_add,add_zero] at H
  exact eq_neg_of_add_eq_zero_right H

end RawLieAdjoint

namespace RawLieAdjoint
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

lemma infinitesimal_triangular {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (v : E₀) (i j : Fin n) (hji : j ≤ i) :
    b.equivFun (infinitesimal (G := G) (E₀ := E₀) v (b i)) j = 0 := by
  let ell : E₀ →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    b.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
  have hd₀ := ((infinitesimal_hasDerivAt (G := G) v).clm_apply
    (hasDerivAt_const (0 : ℝ) (b i))).sub_const (b i)
  have hd := ell.hasFDerivAt.comp_hasDerivAt 0 hd₀
  have he : (fun t : ℝ => ell (adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve v t) (b i) - b i)) =
      fun _ => (0 : ℝ) := funext (fun t => hb (RawLieIntegration.curve v t) i j hji)
  change HasDerivAt (fun t : ℝ => ell (adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve v t) (b i) - b i))
    (ell (infinitesimal (G := G) (E₀ := E₀) v (b i) + adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve v 0) 0)) 0 at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  change ell (infinitesimal (G := G) (E₀ := E₀) v (b i)) = 0
  simpa only [map_zero,add_zero] using hh

lemma infinitesimal_axis_row {n : ℕ} (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (i j : Fin n) (hji : j ≤ i) (x : E₀) :
    b.equivFun (infinitesimal (G := G) (E₀ := E₀) (b i) x) j = 0 := by
  rw [infinitesimal_antisymm,map_neg,Pi.neg_apply,infinitesimal_triangular b hb x i j hji,neg_zero]

lemma infinitesimal_nilpotent {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (v : E₀) :
    (infinitesimal (G := G) (E₀ := E₀) v)^s = 0 :=
  RawNilpotentPolynomial.generator_nilpotent
    (fun t => adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve v t))
    (by erw [RawLieIntegration.curve_zero,adjoint_one]) _ (infinitesimal_hasDerivAt (G := G) v) s
    (fun _ => adjoint_sub_one_nilpotent hstop _)

lemma adjoint_curve_eq_sum {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (v : E₀) (t : ℝ) :
    adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve v t) =
      ∑ k ∈ Finset.range (s+1), ((Nat.factorial k : ℝ)⁻¹ * t^k) •
        (infinitesimal (G := G) (E₀ := E₀) v)^k := by
  apply RawNilpotentPolynomial.oneParameter_polynomial
    (fun t => adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve v t))
    (by erw [RawLieIntegration.curve_zero,adjoint_one])
    (fun t u => by erw [RawLieIntegration.curve_add,adjoint_mul])
    _ (infinitesimal_hasDerivAt (G := G) v)
  exact pow_eq_zero_of_le (Nat.le_succ s) (infinitesimal_nilpotent hstop v)

lemma adjoint_axis_row {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀)
    (hb : ∀ g : G, RawLinearBasis.Triangular b (adjoint (G := G) (E₀ := E₀) g).toLinearMap)
    (i j : Fin n) (hji : j ≤ i) (x : E₀) (t : ℝ) :
    b.equivFun (adjoint (G := G) (E₀ := E₀) (RawLieIntegration.curve (b i) t) x) j = b.equivFun x j := by
  let N := infinitesimal (G := G) (E₀ := E₀) (b i)
  have hk : ∀ k : ℕ, k ≠ 0 → b.equivFun ((N^k) x) j = 0 := by
    intro k hk
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ',mul_apply_eq_comp]
    exact infinitesimal_axis_row b hb i j hji _
  rw [adjoint_curve_eq_sum hstop]
  simp only [sum_apply,smul_apply,map_sum,map_smul,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk0 hk1
    rw [show b.equivFun (((infinitesimal (G := G) (E₀ := E₀) (b i))^k) x) j = 0 from hk k hk1,mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.succ_pos s))).elim

end RawLieAdjoint

namespace RawLieAdjoint
open RawPolynomial RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)

lemma polynomial_adjoint_curve {σ : Type*} {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀) (v : E₀)
    {f : (σ → ℝ) → E₀} {t : (σ → ℝ) → ℝ}
    (hf : IsPolyVec b f) (ht : IsPoly t) :
    IsPolyVec b (fun a => adjoint (G := G) (E₀ := E₀) (curve v (t a)) (f a)) := by
  let N := infinitesimal (G := G) (E₀ := E₀) v
  have H := isPolyVec_sum (Finset.range (s+1))
    (fun k a => ((Nat.factorial k : ℝ)⁻¹ * t a ^ k) • (N^k) (f a))
    (fun k _ => IsPolyVec.smul ((isPoly_const _).mul (ht.pow k)) (hf.linear (N^k).toLinearMap))
  apply H.congr
  intro a
  rw [adjoint_curve_eq_sum hstop]
  simp only [sum_apply,smul_apply,N]

lemma polynomial_adjoint_orderedAxes_inv {σ : Type*} {n s m : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀) (v : Fin m → E₀)
    {f : (σ → ℝ) → E₀} {t : (σ → ℝ) → (Fin m → ℝ)}
    (hf : IsPolyVec b f) (ht : ∀ i, IsPoly (fun a => t a i)) :
    IsPolyVec b (fun a => adjoint (G := G) (E₀ := E₀) (orderedAxes v (t a))⁻¹ (f a)) := by
  induction m generalizing f with
  | zero =>
    apply hf.congr
    intro a
    simp [orderedAxes,adjoint_one]
  | succ m ih =>
    have hg := polynomial_adjoint_curve hstop b (v 0) hf (ht 0).neg
    have H := ih (fun i => v i.succ) hg (fun i => ht i.succ)
    apply H.congr
    intro a
    erw [orderedAxes_succ,mul_inv_rev,adjoint_mul,← curve_neg]
    rfl

lemma polynomial_adjoint_axisTail_inv {σ : Type*} {n s m : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀) (v : Fin m → E₀) (i : Fin m)
    {f : (σ → ℝ) → E₀} {t : (σ → ℝ) → (Fin m → ℝ)}
    (hf : IsPolyVec b f) (ht : ∀ i, IsPoly (fun a => t a i)) :
    IsPolyVec b (fun a => adjoint (G := G) (E₀ := E₀) (axisTail v (t a) i)⁻¹ (f a)) := by
  induction m generalizing f with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact polynomial_adjoint_orderedAxes_inv hstop b (fun k => v k.succ) hf (fun k => ht k.succ)
    · exact ih (fun k => v k.succ) j hf (fun k => ht k.succ)

lemma polynomial_normalizedAxes_column {n s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (b : Module.Basis (Fin n) ℝ E₀) (i j : Fin n) :
    IsPoly (fun a : Fin n → ℝ => b.equivFun
      (adjoint (G := G) (E₀ := E₀) (axisTail b a i)⁻¹ (b i)) j) :=
  polynomial_adjoint_axisTail_inv hstop b b i (isPolyVec_const b (b i))
    (fun k => isPoly_coordinate k) j
end RawLieAdjoint
end

end OAI

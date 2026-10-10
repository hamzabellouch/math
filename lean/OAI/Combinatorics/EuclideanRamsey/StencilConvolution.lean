import OAI.Combinatorics.EuclideanRamsey.RationalConvolution

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

namespace EuclideanRamsey
open scoped BigOperators

lemma stencil_taylor_uniform {ι : Type uIndex} {k : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ x,
      |t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x| ≤ K/t := by
  obtain ⟨K,hK,hTaylor⟩ := compact_taylor_bound hb hbc
  refine ⟨∑ γ ∈ S, |q γ| *K*‖v γ‖^3,Finset.sum_nonneg (fun _ _ => by positivity),?_⟩
  intro t ht x
  have hl := linear_moment_contract S q v (fderiv ℝ b x)
  simp only [hfirst,zero_mul,Finset.sum_const_zero] at hl
  have hb' := bilinear_moment_contract S q v (hessianB b x)
  simp only [hsecond,hessianB_eq] at hb'
  let r (γ : ι) := b (x+(-t⁻¹) • v γ)-b x-
    fderiv ℝ b x ((-t⁻¹) • v γ)-
    (1/2:ℝ)*iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ]
  have hr (γ : ι) : |r γ| ≤ K*(t⁻¹)^3*‖v γ‖^3 := by
    have hh := hTaylor x ((-t⁻¹) • v γ)
    simpa only [r,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos ht,mul_pow,
      mul_assoc] using hh
  have hrEq : t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x =
      t^2*∑ γ ∈ S,q γ*r γ := by
    have hscale (γ : ι) : iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ] =
        (t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ] := by
      simp only [← hessianB_eq,map_smul,_root_.smul_apply,smul_eq_mul]
      ring
    simp only [r,mul_sub,Finset.sum_sub_distrib,map_smul,smul_eq_mul,hscale]
    have hz : ∑ γ ∈ S,q γ*b x = 0 := by rw [← Finset.sum_mul,hzero,zero_mul]
    have h1 : ∑ γ ∈ S,q γ*(-t⁻¹*fderiv ℝ b x (v γ)) = 0 := by
      calc
        _ = -t⁻¹*(∑ γ ∈ S,q γ*fderiv ℝ b x (v γ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro γ hγ; ring
        _ = 0 := by rw [hl,mul_zero]
    have h2 : ∑ γ ∈ S,q γ*((1/2:ℝ)*((t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ])) =
        (t⁻¹)^2*stencilDifferential C b x := by
      unfold stencilDifferential
      rw [← hb']
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      ring
    rw [hz,h1,h2]
    field_simp
    ring
  rw [hrEq,abs_mul,abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ t^2 * ∑ γ ∈ S, |q γ| *|r γ| := by
      gcongr
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun γ => q γ*r γ) S
    _ ≤ t^2 * ∑ γ ∈ S, |q γ| *(K*(t⁻¹)^3*‖v γ‖^3) := by
      gcongr with γ hγ
      exact hr γ
    _ = (∑ γ ∈ S,|q γ| *K*‖v γ‖^3)/t := by
      rw [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro γ hγ
      field_simp

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Topology

lemma stencilDifferential_continuous {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    Continuous (stencilDifferential C b) := by
  have hh := hb.continuous_iteratedFDeriv (m := 2) (by norm_cast)
  unfold stencilDifferential
  fun_prop

lemma stencilDifferential_support {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) : Function.support (stencilDifferential C b) ⊆ tsupport b := by
  intro x hx
  by_contra h
  have hi : x ∉ tsupport (iteratedFDeriv ℝ 2 b) := fun hx => h (tsupport_iteratedFDeriv_subset 2 hx)
  have hz := image_eq_zero_of_notMem_tsupport hi
  exact hx (by simp [stencilDifferential,hz])

lemma stencil_weighted_riemann {ι : Type uIndex} {k d : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ,
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (latticeSample n δ+(-(n:ℝ)⁻¹) • v γ))) 0 *
        gradientWeight U (latticeSample n δ))/(n:ℝ)^k) atTop
      (𝓝 (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x)) := by
  classical
  let f := fun x => max (-stencilDifferential C b x) 0*gradientWeight U x
  let g := fun (n : ℕ) x => max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) 0*
    gradientWeight U x
  have hc : Continuous f := by
    have hh := stencilDifferential_continuous C hb
    unfold f gradientWeight
    fun_prop
  have hs : Function.support f ⊆ tsupport b := by
    intro x hx
    by_contra h
    have hd : stencilDifferential C b x = 0 := by
      by_contra hh
      exact h (stencilDifferential_support C b hh)
    exact hx (by simp [f,hd])
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hbc hs
  obtain ⟨r,hr,hbr⟩ := hbc.exists_pos_le_norm
  let V := ∑ γ ∈ S,‖v γ‖
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv (γ : ι) (hγ : γ ∈ S) : ‖v γ‖ ≤ V := Finset.single_le_sum (fun _ _ => norm_nonneg _) hγ
  let R := r+V+1
  have hR : 0 < R := by dsimp [R]; linarith
  have hfr : Function.support f ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra h
    have hxr : r < ‖x‖ := by dsimp [R] at h; linarith
    have hnb : x ∉ tsupport b := by
      apply notMem_tsupport_iff_eventuallyEq.mpr
      filter_upwards [(continuous_norm.continuousAt.eventually (eventually_gt_nhds hxr))] with y hy
      exact hbr y hy.le
    exact hnb (hs hx)
  have hgr (n : ℕ) : Function.support (g n) ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra h
    have hRx : R < ‖x‖ := lt_of_not_ge h
    have hz : g n x = 0 := by
      by_cases hn : n = 0
      · simp [g,hn]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hni : |(n:ℝ)⁻¹| ≤ 1 := by rw [abs_inv,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hn1
      have hsum : ∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ) = 0 := by
        apply Finset.sum_eq_zero
        intro γ hγ
        have hnorm : r ≤ ‖x+(-(n:ℝ)⁻¹) • v γ‖ := by
          have hshift : ‖(-(n:ℝ)⁻¹) • v γ‖ ≤ V := by
            rw [norm_smul,Real.norm_eq_abs,abs_neg]
            exact (mul_le_mul_of_nonneg_right hni (norm_nonneg _)).trans (by simpa using hv γ hγ)
          have hx' : ‖x‖ ≤ ‖x+(-(n:ℝ)⁻¹) • v γ‖+‖(-(n:ℝ)⁻¹) • v γ‖ := by
            simpa only [add_sub_cancel_left] using norm_le_norm_add_norm_sub (x+(-(n:ℝ)⁻¹) • v γ) x
          dsimp [R] at hRx
          linarith
        rw [hbr _ hnorm,mul_zero]
      dsimp only [g]
      rw [hsum]
      simp
    exact hx hz
  obtain ⟨W,hW⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_bound_of_continuousOn
    (show Continuous (gradientWeight U) by unfold gradientWeight; fun_prop).continuousOn
  obtain ⟨K,hK,hTaylor⟩ := stencil_taylor_uniform S q v C hzero hfirst hsecond hb hbc
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp [hR.le]))
  apply lattice_riemann_perturb f g hc hfc hR hfr hgr (fun n => K*W/(n:ℝ))
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  · intro n hn x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin k → ℝ) R
    · have hw : |gradientWeight U x| ≤ W := by simpa [Real.norm_eq_abs] using hW x hx
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have he := hTaylor n hn0 x
      have hm := abs_max_sub_max_le_abs
        (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) (-stencilDifferential C b x) 0
      have hm' : |max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) 0-
          max (-stencilDifferential C b x) 0| ≤ K/n := by
        apply hm.trans
        simpa only [neg_sub_neg,abs_sub_comm] using he
      dsimp [g,f]
      rw [← sub_mul,abs_mul]
      calc
        _ ≤ (K/n)*W := mul_le_mul hm' hw (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have hf0 : f x = 0 := by by_contra hh; exact hx (hfr hh)
      have hg0 : g n x = 0 := by by_contra hh; exact hx (hgr n hh)
      rw [hf0,hg0,sub_self,abs_zero]
      positivity

end EuclideanRamsey

namespace EuclideanRamsey
open Filter MeasureTheory
open scoped BigOperators Topology

theorem exists_discrete_smoothing {k d : ℕ} (S : Finset (Fin k → ℤ))
    (q : (Fin k → ℤ) → ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*(γ j:ℝ) = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*(γ j:ℝ)*(γ l:ℝ) = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hI : 0 < ∫ x,b x)
    {η : ℝ} (hη : (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x) < η*∫ x,b x) :
    ∃ (n : ℕ) (a : (Fin k → ℤ) → ℝ), 1 ≤ n ∧ Function.HasFiniteSupport a ∧
      0 < (∑' γ,a γ)/(n:ℝ)^2 ∧
      (∑' δ,max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ)) <
        η*((∑' γ,a γ)/(n:ℝ)^2) := by
  have hZ := lattice_riemann hb.continuous hbc
  have hN := stencil_weighted_riemann S q (fun γ j => (γ j:ℝ)) C U hzero hfirst hsecond hb hbc
  have he := hN.eventually_lt (tendsto_const_nhds.mul hZ) hη
  have hp := (tendsto_const_nhds.eventually_lt hZ hI)
  obtain ⟨n,hn,hp,he⟩ := (eventually_ge_atTop 1 |>.and (hp.and he)).exists
  let a := fun γ : Fin k → ℤ => b (latticeSample n γ)
  have hnf : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : Function.HasFiniteSupport a := latticeSample_finite_support (by omega) hbc
  have hshift (δ γ : Fin k → ℤ) : latticeSample n δ+(-(n:ℝ)⁻¹) • (fun j => (γ j:ℝ)) =
      latticeSample n (δ-γ) := by
    ext j
    simp only [latticeSample,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Int.cast_sub]
    ring
  simp only [hshift] at he
  have hscale (δ : Fin k → ℤ) :
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ) =
      (n:ℝ)^2*(max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ)) := by
    rw [← mul_neg,← mul_zero ((n:ℝ)^2),← mul_max_of_nonneg _ _ (sq_nonneg (n:ℝ))]
    rw [mul_assoc, mul_zero]
  change (∑' δ,max (-((n:ℝ)^2*∑ γ ∈ S,q γ*a (δ-γ))) 0*
    gradientWeight U (latticeSample n δ))/(n:ℝ)^k < η*((∑' γ,a γ)/(n:ℝ)^k) at he
  simp only [hscale,tsum_mul_left] at he
  have hp' : 0 < ∑' γ,a γ := (div_pos_iff_of_pos_right (pow_pos hnf k)).mp hp
  refine ⟨n,a,hn,ha,div_pos hp' (sq_pos_of_pos hnf),?_⟩
  have hh : (n:ℝ)^2*(∑' δ,max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*
      gradientWeight U (latticeSample n δ)) < η*(∑' γ,a γ) := by
    apply (div_lt_div_iff_of_pos_right (pow_pos hnf k)).mp
    simpa only [mul_div_assoc] using he
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (sq_pos_of_pos hnf)).mpr
  simpa only [mul_comm] using hh

end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators

lemma cosetPushforward_mul {k : ℕ} (Λ : AddSubgroup (Lattice k)) (ν b : LatticeRing k)
    (hν : cosetPushforward Λ ν = 0) : cosetPushforward Λ (ν*b) = 0 := by
  have he : AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' Λ) ν = 0 := by
    apply AddMonoidAlgebra.coeff_injective
    exact hν
  change (AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' Λ) (ν*b)).coeff = 0
  rw [AddMonoidAlgebra.mapDomain_mul,he,zero_mul]
  rfl

theorem rational_smoothing {k d s : ℕ} (hd : 1 ≤ d)
    (Λ : Fin s → AddSubgroup (Lattice k)) (ν : LatticeRing k)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose = (1 : Matrix (Fin d) (Fin d) ℝ))
    (hcos : ∀ i,cosetPushforward (Λ i) ν = 0)
    (hzero : mass ν = 0) (hfirst : ∀ j,firstMoment ν j = 0)
    (hsecond : ∀ j l,secondMoment ν j l = C j l)
    (η : ℝ) (hη : 0 < η) :
    ∃ (n : ℕ) (μ : LatticeRing k) (ζ : ℚ), 1 ≤ n ∧ 0 < ζ ∧
      (∀ i,cosetPushforward (Λ i) μ = 0) ∧ mass μ = 0 ∧
      (∀ j,firstMoment μ j = 0) ∧
      (∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l) ∧
      (∑' δ : Lattice k,max (-(μ.coeff δ:ℝ)) 0*gradientWeight U (latticeSample n δ)) < η*ζ := by
  classical
  have hC' : (C.map (Rat.cast : ℚ → ℝ)).IsSymm := by
    ext j l
    change (C l j:ℝ) = (C j l:ℝ)
    exact congrArg Rat.cast (congrFun (congrFun hC j) l)
  obtain ⟨b,hb,hbc,hb0,hbI,hbη⟩ := compact_smoothing k d hd (C.map (Rat.cast : ℚ → ℝ)) U hC' hU η hη
  have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ) = 0 := by
    exact_mod_cast hzero
  have hf (j : Fin k) : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*(γ j:ℝ) = 0 := by
    exact_mod_cast hfirst j
  have hs (j l : Fin k) : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*(γ j:ℝ)*(γ l:ℝ) = (C j l:ℝ) := by
    exact_mod_cast hsecond j l
  obtain ⟨n,a,hn,ha,hap,han⟩ := exists_discrete_smoothing ν.coeff.support
    (fun γ => (ν.coeff γ:ℝ)) (C.map (Rat.cast : ℚ → ℝ)) U hz hf hs hb hbc hbI hbη
  obtain ⟨p,hp0,hpη⟩ := rationalize_convolution ν (fun δ => gradientWeight U (latticeSample n δ))
    ((n:ℝ)^2) η ha hap han
  let ζ : ℚ := mass p/(n:ℚ)^2
  have hζ : (ζ:ℝ) = ((mass p : ℚ):ℝ)/(n:ℝ)^2 := by simp [ζ]
  have hζ0 : 0 < ζ := by
    have hp' : (0:ℝ) < (ζ:ℝ) := by simpa only [hζ,mass] using hp0
    exact_mod_cast hp'
  refine ⟨n,ν*p,ζ,hn,hζ0,fun i => cosetPushforward_mul (Λ i) ν p (hcos i),?_,?_,?_,?_⟩
  · simp [hzero]
  · intro j
    simp [firstMoment_mul,hzero,hfirst]
  · intro j l
    simp only [secondMoment_mul,hzero,hfirst,hsecond,zero_mul,zero_add,add_zero]
    dsimp [ζ]
    ring
  · simpa only [hζ,mass] using hpη

end EuclideanRamsey

end

end OAI

import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Multiplier2
import OAI.Analysis.CoulombIonization.Fermionic.MultiplierError

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LipschitzResidualBase_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma positive_map_cauchy_re {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive) (F G : V) :
    (⟪G, B F⟫_ℂ).re ^ 2 ≤ (⟪F, B F⟫_ℂ).re * (⟪G, B G⟫_ℂ).re := by
  have hs : (⟪F, B G⟫_ℂ).re = (⟪G, B F⟫_ℂ).re := by
    have hh := hB.isSymmetric F G
    change ⟪B F,G⟫_ℂ = ⟪F,B G⟫_ℂ at hh
    rw [← hh]
    exact inner_re_symm (𝕜 := ℂ) _ _
  have hp (t : ℝ) : 0 ≤ (⟪F, B F⟫_ℂ).re +
      2*t*(⟪G, B F⟫_ℂ).re+t*t*(⟪G, B G⟫_ℂ).re := by
    have hh := hB.re_inner_nonneg_right (F+(t:ℂ) • G)
    change 0 ≤ (⟪F+(t:ℂ) • G,B (F+(t:ℂ) • G)⟫_ℂ).re at hh
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, hs] at hh
    nlinarith
  have hd := discrim_le_zero (a := (⟪G,B G⟫_ℂ).re)
    (b := 2*(⟪G,B F⟫_ℂ).re) (c := (⟪F,B F⟫_ℂ).re) (fun t => by
      nlinarith [hp t])
  dsimp [discrim] at hd
  nlinarith

lemma shifted_form_positive {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : V →L[ℂ] H) (A : V →L[ℂ] V) (hs : IsSelfAdjoint A) (E : ℝ)
    (hlow : ∀ F, E*‖j F‖^2 ≤ (⟪F,A F⟫_ℂ).re) :
    (A-(E:ℂ) • (j.adjoint.comp j)).IsPositive := by
  have hBs : IsSelfAdjoint (A-(E:ℂ) • (j.adjoint.comp j)) :=
    IsSelfAdjoint.sub (R := V →L[ℂ] V) hs
      (IsSelfAdjoint.smul (R := ℂ) (A := V →L[ℂ] V)
        (Complex.conj_ofReal E) j.isPositive_adjoint_comp_self.isSelfAdjoint)
  refine ⟨hBs.isSymmetric,fun F => ?_⟩
  change 0 ≤ (⟪(A-(E:ℂ) • (j.adjoint.comp j)) F,F⟫_ℂ).re
  have hre : (⟪(A-(E:ℂ) • (j.adjoint.comp j)) F,F⟫_ℂ).re =
      (⟪F,(A-(E:ℂ) • (j.adjoint.comp j)) F⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hre]
  simp only [sub_apply,smul_apply,inner_sub_right,inner_smul_right,
    ContinuousLinearMap.comp_apply,j.adjoint_inner_right,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  have hv := norm_sq_eq_re_inner (𝕜 := ℂ) (j F)
  change ‖j F‖^2 = (⟪j F,j F⟫_ℂ).re at hv
  rw [← hv]
  exact sub_nonneg.mpr (hlow F)

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma graphForm_lower {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ} (F : fermionGraph N) :
    energy Z N * ‖fermionGraphValue N F‖ ^ 2 ≤
      (⟪F, coulombFormOperator Z N F⟫_ℂ).re := by
  rw [coulombFormOperator_inner Z N F]
  exact quantum_form_above_sector hZ F

def sectorExcessOperator (Z : ℝ) (N : ℕ) : fermionGraph N →L[ℂ] fermionGraph N :=
  coulombFormOperator Z N-(energy Z N : ℂ) •
    ((fermionGraphValue N).adjoint.comp (fermionGraphValue N))

lemma sectorExcessOperator_pair {N : ℕ} (Z : ℝ) (G F : fermionGraph N) :
    (⟪G,sectorExcessOperator Z N F⟫_ℂ).re =
      (⟪G,coulombFormOperator Z N F⟫_ℂ).re-
        energy Z N*(⟪fermionGraphValue N G,fermionGraphValue N F⟫_ℂ).re := by
  simp only [sectorExcessOperator,sub_apply,
    smul_apply,inner_sub_right,inner_smul_right,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

attribute [local irreducible] sectorExcessOperator

lemma sectorExcessOperator_diagonal {N : ℕ} (Z : ℝ) (F : fermionGraph N) :
    (⟪F,sectorExcessOperator Z N F⟫_ℂ).re =
      formEnergy Z (graphFormVector F)-energy Z N*‖fermionGraphValue N F‖^2 := by
  have hv : (⟪fermionGraphValue N F,fermionGraphValue N F⟫_ℂ).re =
      ‖fermionGraphValue N F‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (fermionGraphValue N F)).symm
  exact (sectorExcessOperator_pair Z F F).trans
    (congrArg₂ (fun u v => u-energy Z N*v) (coulombFormOperator_inner Z N F) hv)

lemma sectorExcessOperator_positive {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    (sectorExcessOperator Z N).IsPositive := by
  unfold sectorExcessOperator
  exact shifted_form_positive (fermionGraphValue N) (coulombFormOperator Z N)
    (coulombFormOperator_selfAdjoint Z N) (energy Z N) (graphForm_lower hZ)

lemma near_minimizer_graph_bound {Z : ℝ} (hZ : 0 ≤ Z) {N : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2=1)
    (hF : formEnergy Z (graphFormVector F) ≤ energy Z N+1) :
    ‖F‖^2 ≤ 4*(|energy Z N| + (N:ℝ)*Z^2+2) := by
  have hc := coulombFormOperator_coercive_bound hZ F
  rw [coulombFormOperator_inner Z N F,hn] at hc
  nlinarith [le_abs_self (energy Z N)]

end Work_LipschitzResidualBase_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma l2_real_multiplier_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g : Lp ℂ 2 μ) (p : X → ℝ) {C : ℝ} (hC : ∀ x, |p x| ≤ C)
    (hg : (g : X → ℂ) =ᵐ[μ] fun x => (p x : ℂ)*f x) :
    ‖g‖^2 ≤ C^2*‖f‖^2 := by
  rw [l2_norm_sq,l2_norm_sq,← integral_const_mul]
  apply integral_mono_ae (Lp.memLp g).norm.integrable_sq
    ((Lp.memLp f).norm.integrable_sq.const_mul _)
  filter_upwards [hg] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) (sq_nonneg _)

lemma complex_two_weight_bound (p q : ℝ) (a b : ℂ) {C D : ℝ}
    (hC : |p| ≤ C) (hD : |q| ≤ D) :
    ‖(p:ℂ)*a+(q:ℂ)*b‖^2 ≤ 2*C^2*‖a‖^2+2*D^2*‖b‖^2 := by
  have hh := norm_add_le ((p:ℂ)*a) ((q:ℂ)*b)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hh
  have hp2 := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hC 2) (sq_nonneg ‖a‖)
  have hq2 := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hD 2) (sq_nonneg ‖b‖)
  have ht := sq_nonneg (|p| * ‖a‖-|q| * ‖b‖)
  have hu : 0 ≤ |p| * ‖a‖+|q| * ‖b‖ := by positivity
  nlinarith [sq_le_sq₀ (norm_nonneg ((p:ℂ)*a+(q:ℂ)*b)) hu |>.2 hh]

lemma l2_two_multiplier_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g h : Lp ℂ 2 μ) (p q : X → ℝ) {C D : ℝ}
    (hC : ∀ x, |p x| ≤ C) (hD : ∀ x, |q x| ≤ D)
    (hh : (h : X → ℂ) =ᵐ[μ] fun x => (p x:ℂ)*f x+(q x:ℂ)*g x) :
    ‖h‖^2 ≤ 2*C^2*‖f‖^2+2*D^2*‖g‖^2 := by
  rw [l2_norm_sq,l2_norm_sq,l2_norm_sq,← integral_const_mul,← integral_const_mul,
    ← integral_add ((Lp.memLp f).norm.integrable_sq.const_mul _)
      ((Lp.memLp g).norm.integrable_sq.const_mul _)]
  apply integral_mono_ae (Lp.memLp h).norm.integrable_sq
    (((Lp.memLp f).norm.integrable_sq.const_mul _).add
      ((Lp.memLp g).norm.integrable_sq.const_mul _))
  filter_upwards [hh] with x hx
  rw [hx]
  exact complex_two_weight_bound _ _ _ _ (hC x) (hD x)

attribute [local irreducible] graphComponent graphFormVector FermionLipschitzMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

lemma FermionLipschitzMultiplier.mass_bound {N : ℕ} (p : FermionLipschitzMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖^2 ≤ C^2*‖fermionGraphValue N F‖^2 := by
  rw [graphValue_norm_sq,graphValue_norm_sq,Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => l2_real_multiplier_bound _ _ p.value hC
    (p.apply_value F s)

lemma FermionLipschitzMultiplier.kinetic_bound {N : ℕ} (p : FermionLipschitzMultiplier N)
    {C : ℝ} (hC : ∀ x, |p.value x| ≤ C) (D : Fin N × Fin 3 → ℝ)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D (i,a))
    (F : fermionGraph N) :
    (∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) (p.apply F)‖^2) ≤
      2*C^2*(∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2)+
        2*(∑ i,∑ a,D (i,a)^2)*‖fermionGraphValue N F‖^2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun a _ =>
      l2_two_multiplier_bound (graphComponent s (some (i,a)) F)
        (graphComponent s none F) (graphComponent s (some (i,a)) (p.apply F))
        p.value (fun x => lineDeriv ℝ p.value x (direction i a)) hC (hD i a)
        (p.apply_gradient F s i a)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul] at hh
  rw [graphValue_norm_sq]
  convert hh using 1

lemma graph_multiplier_arithmetic {M K M' K' f f' C S : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (hm : M' ≤ C^2*M) (hk : K' ≤ 2*C^2*K+2*S*M)
    (he : f=M+K) (he' : f'=M'+K') : f' ≤ (3*C^2+2*S)*f := by
  nlinarith [mul_nonneg (sq_nonneg C) hK,mul_nonneg hS hK,
    mul_nonneg (sq_nonneg C) hM]

theorem FermionLipschitzMultiplier.graph_bound {N : ℕ} (p : FermionLipschitzMultiplier N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : fermionGraph N, ‖p.apply F‖^2 ≤ C*‖F‖^2 := by
  classical
  obtain ⟨C,hC⟩ := p.bound
  let D : Fin N × Fin 3 → ℝ := fun ia => p.constant * ‖direction ia.1 ia.2‖
  have hD : ∀ ia x, |lineDeriv ℝ p.value x (direction ia.1 ia.2)| ≤ D ia := by
    intro ia x
    simpa only [Real.norm_eq_abs] using
      (norm_lineDeriv_le_of_lipschitz ℝ p.lipschitz (x₀ := x) (v := direction ia.1 ia.2))
  let S : ℝ := ∑ i : Fin N,∑ a : Fin 3,D (i,a)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  refine ⟨3*C^2+2*S,by positivity,fun F => ?_⟩
  have hm := p.mass_bound hC F
  have hk := p.kinetic_bound hC D (fun i a x => hD (i,a) x) F
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  exact graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))

end CoulombAtom

end

end OAI

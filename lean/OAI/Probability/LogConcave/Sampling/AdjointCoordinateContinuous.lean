import Mathlib
import OAI.Probability.LogConcave.Sampling.DirectionalAdjointCoordinate
import OAI.Probability.LogConcave.JetEstimates.Lipschitz

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma adjointCoordinate_continuous {d : ℕ} {H f : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hf : PolyC1 f) (v : Point d) :
    Continuous (adjointCoordinate H v f) :=
  (hf.directional_continuous v).neg.add
    (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hf.continuous)

lemma adjointCoordinate_growth {d : ℕ} {H f : Point d → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (v : Point d) :
    HasPolynomialGrowth (adjointCoordinate H v f) := by
  have hs : HasPolynomialGrowth (directional v H) := by
    simpa only [HasPolynomialGrowth,directional_gradient] using growth_inner_gradient hL v
  exact Appell.HasGrowth.add (by
    simpa only [HasPolynomialGrowth,Appell.HasGrowth,neg_one_mul] using
      Appell.HasGrowth.mul (growth_const (-1:ℝ)) (hf.derivative_growth v))
    (Appell.HasGrowth.mul hs hf.growth)

lemma integrable_adjointCoordinate_mul {d : ℕ} {H f g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f) (hg : PolyC1 g) (v : Point d) :
    Integrable (fun x => adjointCoordinate H v f x*g x) (gibbs H) :=
  integrable_polynomial_gibbs hH.continuous ht
    ((adjointCoordinate_continuous hH hf v).mul hg.continuous)
    (Appell.HasGrowth.mul (adjointCoordinate_growth hL hf v) hg.growth)

theorem tensorAdjoint_energy_identity {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : ι → Point d)
    (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i)) (hg : ∀i,PolyC1 (V i))
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    (∫x,(tensorAdjoint H b V x)^2 ∂gibbs H)=
      ∑i,∑j,∫x,directional (b i) (V j) x*directional (b j) (V i) x+
        directional (b i) (directional (b j) H) x*V i x*V j x ∂gibbs H := by
  have hc : ContDiff ℝ 1 H := hH.of_le (by simp)
  have hA := polyC1_tensorAdjoint hH hL b hg (fun i => hD i i)
  have hs (i j : ι) : Integrable (fun x =>
      directional (b i) (directional (b j) H) x*V i x*V j x) (gibbs H) := by
    have hp := polyC1_directional_potential hH hL (b j)
    exact integrable_polynomial_gibbs hc.continuous ht
      (((hp.directional_continuous (b i)).mul (hg i).continuous).mul (hg j).continuous)
      (Appell.HasGrowth.mul (Appell.HasGrowth.mul (hp.derivative_growth (b i)) (hg i).growth) (hg j).growth)
  have hd (i j : ι) : Integrable (fun x => directional (b i) (V j) x*directional (b j) (V i) x) (gibbs H) :=
    integrable_polynomial_gibbs hc.continuous ht
      ((hD i j).continuous.mul (hD j i).continuous)
      (Appell.HasGrowth.mul (hD i j).growth (hD j i).growth)
  have ha (i j : ι) : Integrable (fun x => adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x) (gibbs H) :=
    integrable_adjointCoordinate_mul hc ht hL (hD i j) (hg i) (b j)
  calc
    _ = ∫x,tensorAdjoint H b V x*tensorAdjoint H b V x ∂gibbs H := by simp only [pow_two]
    _ = ∑i,∫x,V i x*directional (b i) (tensorAdjoint H b V) x ∂gibbs H :=
      tensorAdjoint_pairing hc ht hL hg hA b
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he : (fun x => V i x*directional (b i) (tensorAdjoint H b V) x)=
          fun x => ∑j,(adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x+
            directional (b i) (directional (b j) H) x*V i x*V j x) := by
        rw [directional_tensorAdjoint hH hV]
        funext x
        simp only [tensorAdjoint,mul_add,Finset.mul_sum,Finset.sum_add_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
      rw [he,integral_finsetSum Finset.univ
        (f:=fun j x => adjointCoordinate H (b j) (directional (b i) (V j)) x*V i x+
          directional (b i) (directional (b j) H) x*V i x*V j x)
        (fun j _ => (ha i j).add (hs i j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_add (ha i j) (hs i j),integral_add (hd i j) (hs i j),
        adjointCoordinate_pairing hc ht hL (hD i j) (hg i) (b j)]

end LogConcaveSampling
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

lemma matrix_cross_le_squares {ι : Type*} [Fintype ι] (a : ι → ι → ℝ) :
    (∑i,∑j,a i j*a j i) ≤ ∑i,∑j,(a i j)^2 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈(Finset.univ:Finset ι)) =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈(Finset.univ:Finset ι)) =>
      show 2*(a i j*a j i) ≤ (a i j)^2+(a j i)^2 by nlinarith [sq_nonneg (a i j-a j i)]))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have he : (∑i,∑j,(a j i)^2)=∑i,∑j,(a i j)^2 := Finset.sum_comm
  rw [he] at hh
  linarith

lemma directional_hessian {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v x : Point d) :
    directional u (directional v H) x=inner ℝ (fderiv ℝ (gradient H) x u) v := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradient H) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp (hH.fderiv_right (by simp))
  have he : directional v H=(fun z => inner ℝ v (gradient H z)) := by
    funext z
    rw [directional_gradient,real_inner_comm]
  rw [he]
  have hd := (innerSL ℝ v).hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)
  change (fderiv ℝ (fun z => (innerSL ℝ v) (gradient H z)) x) u=_
  have hde : fderiv ℝ (fun z => (innerSL ℝ v) (gradient H z)) x=
      (innerSL ℝ v).comp (fderiv ℝ (gradient H) x) := hd.fderiv
  rw [hde]
  simp only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,real_inner_comm]

lemma hessian_quadratic_le {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {K : ℝ≥0} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (a : ι → ℝ) (x : Point d) :
    (∑i,∑j,directional (b i) (directional (b j) H) x*a i*a j) ≤
      (K:ℝ)*∑i,(a i)^2 := by
  classical
  let z : Point d := ∑i,a i • b i
  have hz (i : ι) : inner ℝ (b i) z=a i := by
    simp [z,inner_sum,inner_smul_right,orthonormal_iff_ite.mp b.orthonormal]
  have hn : ‖z‖^2=∑i,(a i)^2 := by simpa only [hz] using (b.sum_sq_inner_right z).symm
  have he : (∑i,∑j,directional (b i) (directional (b j) H) x*a i*a j)=
      inner ℝ (fderiv ℝ (gradient H) x z) z := by
    simp only [z,map_sum,map_smul,directional_hessian hH,sum_inner,inner_smul_left,
      inner_sum,inner_smul_right,starRingEnd_apply,star_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hsym := congrFun (directional_commute hH (b i) (b j)) x
    rw [directional_hessian hH,directional_hessian hH] at hsym
    rw [hsym]
    ring
  rw [he]
  have h₁ := real_inner_le_norm (fderiv ℝ (gradient H) x z) z
  have h₂ := (fderiv ℝ (gradient H) x).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hL) z
  exact h₁.trans ((mul_le_mul_of_nonneg_right h₂ (norm_nonneg z)).trans_eq (by calc
    (K:ℝ)*‖z‖*‖z‖=(K:ℝ)*‖z‖^2 := by ring
    _ = _ := by rw [hn]))

end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma integrable_directional_square_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (b : ι → Point d)
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    Integrable (fun x => ∑i,∑j,(directional (b i) (V j) x)^2) (gibbs H) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact integrable_polynomial_gibbs hH ht ((hD i j).continuous.pow 2)
    (Appell.HasGrowth.pow (hD i j).growth 2)

lemma integrable_square_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (hV : ∀i,PolyC1 (V i)) :
    Integrable (fun x => ∑i,(V i x)^2) (gibbs H) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  exact integrable_polynomial_gibbs hH ht ((hV i).continuous.pow 2)
    (Appell.HasGrowth.pow (hV i).growth 2)

theorem tensorAdjoint_energy_le {d : ℕ} {ι : Type*} [Fintype ι]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i)) (hg : ∀i,PolyC1 (V i))
    (hD : ∀i j,PolyC1 (directional (b i) (V j))) :
    (∫x,(tensorAdjoint H b V x)^2 ∂gibbs H) ≤
      (∫x,∑i,∑j,(directional (b i) (V j) x)^2 ∂gibbs H)+
      (K:ℝ)*(∫x,∑i,(V i x)^2 ∂gibbs H) := by
  let W : ι → ι → Point d → ℝ := fun i j x =>
    directional (b i) (V j) x*directional (b j) (V i) x+
    directional (b i) (directional (b j) H) x*V i x*V j x
  have hi (i j : ι) : Integrable (W i j) (gibbs H) := by
    have hp := polyC1_directional_potential hH hL (b j)
    exact (integrable_polynomial_gibbs hH.continuous ht
      ((hD i j).continuous.mul (hD j i).continuous)
      (Appell.HasGrowth.mul (hD i j).growth (hD j i).growth)).add
      (integrable_polynomial_gibbs hH.continuous ht
        (((hp.directional_continuous (b i)).mul (hg i).continuous).mul (hg j).continuous)
        (Appell.HasGrowth.mul (Appell.HasGrowth.mul (hp.derivative_growth (b i)) (hg i).growth) (hg j).growth))
  have hirow (i : ι) : Integrable (fun x => ∑j,W i j x) (gibbs H) :=
    integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have hiW : Integrable (fun x => ∑i,∑j,W i j x) (gibbs H) :=
    integrable_finsetSum Finset.univ (fun i _ => hirow i)
  have hiD := integrable_directional_square_sum hH.continuous ht b hD
  have hiV := integrable_square_sum hH.continuous ht hg
  calc
    _ = ∑i,∑j,∫x,W i j x ∂gibbs H := tensorAdjoint_energy_identity hH ht hL b hV hg hD
    _ = ∫x,∑i,∑j,W i j x ∂gibbs H := by
      rw [integral_finsetSum Finset.univ (fun i _ => hirow i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    _ ≤ ∫x,((∑i,∑j,(directional (b i) (V j) x)^2)+(K:ℝ)*(∑i,(V i x)^2)) ∂gibbs H := by
      apply integral_mono hiW (hiD.add (hiV.const_mul (K:ℝ)))
      intro x
      simp only [W,Finset.sum_add_distrib]
      exact add_le_add (matrix_cross_le_squares (fun i j => directional (b i) (V j) x))
        (hessian_quadratic_le hH hL b (fun i => V i x) x)
    _ = _ := by
      rw [integral_add (f:=fun x => ∑i,∑j,(directional (b i) (V j) x)^2)
        (g:=fun x => (K:ℝ)*(∑i,(V i x)^2)) hiD (hiV.const_mul (K:ℝ)),integral_const_mul]

theorem tensorAdjoint_frobenius_squared {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {H : Point d → ℝ} {V : κ → ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀a i,ContDiff ℝ (⊤ : ℕ∞) (V a i)) (hg : ∀a i,PolyC1 (V a i))
    (hD : ∀a i j,PolyC1 (directional (b i) (V a j))) :
    (∑a,∫x,(tensorAdjoint H b (V a) x)^2 ∂gibbs H) ≤
      (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)+
      (K:ℝ)*(∑a,∫x,∑i,(V a i x)^2 ∂gibbs H) := by
  simpa only [Finset.sum_add_distrib,Finset.mul_sum] using
    Finset.sum_le_sum (s:=Finset.univ) (fun a (_ : a∈(Finset.univ:Finset κ)) =>
      tensorAdjoint_energy_le hH ht hL b (hV a) (hg a) (hD a))

theorem tensorAdjoint_frobenius_l2 {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {H : Point d → ℝ} {V : κ → ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (b : OrthonormalBasis ι ℝ (Point d))
    (hV : ∀a i,ContDiff ℝ (⊤ : ℕ∞) (V a i)) (hg : ∀a i,PolyC1 (V a i))
    (hD : ∀a i j,PolyC1 (directional (b i) (V a j))) :
    Real.sqrt (∑a,∫x,(tensorAdjoint H b (V a) x)^2 ∂gibbs H) ≤
      Real.sqrt (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)+
      Real.sqrt (K:ℝ)*Real.sqrt (∑a,∫x,∑i,(V a i x)^2 ∂gibbs H) := by
  have hh := Real.sqrt_le_sqrt (tensorAdjoint_frobenius_squared hH ht hL b hV hg hD)
  have hs0 (a b : ℝ) : Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have ha := Real.sq_sqrt' (x:=a)
      have hb := Real.sq_sqrt' (x:=b)
      have hma := le_max_left a 0
      have hmb := le_max_left b 0
      have hp := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
      nlinarith
  have hs := hs0 (∑a,∫x,∑i,∑j,(directional (b i) (V a j) x)^2 ∂gibbs H)
    ((K:ℝ)*(∑a,∫x,∑i,(V a i x)^2 ∂gibbs H))
  rw [Real.sqrt_mul K.coe_nonneg] at hs
  exact hh.trans hs
end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma directional_prod {d : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → Point d → ℝ} (hf : ∀i∈s,Differentiable ℝ (f i)) (v : Point d) :
    directional v (fun x => ∏i∈s,f i x)=fun x =>
      ∑i∈s,(∏j∈s.erase i,f j x)*directional v (f i) x := by
  funext x
  have hh := (HasFDerivAt.finsetProd (fun i hi => (hf i hi x).hasFDerivAt)).fderiv
  simpa only [directional,sum_apply,smul_apply,smul_eq_mul] using
    congrArg (fun A : Point d →L[ℝ] ℝ => A v) hh

namespace PolyC1
lemma const {d : ℕ} (c : ℝ) : PolyC1 (fun _ : Point d => c) := by
  refine ⟨contDiff_const,growth_const c,fun v => ?_⟩
  have he : directional v (fun _ : Point d => c)=fun _ => 0 := by
    funext x
    simp [directional]
  rw [he]
  exact growth_const 0

lemma prod {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Point d → ℝ}
    (hf : ∀i∈s,PolyC1 (f i)) : PolyC1 (fun x => ∏i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (d:=d) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hf i (Finset.mem_insert_self i s)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
end PolyC1

theorem adjointCoordinate_product_pairing {d : ℕ} {ι : Type*} [DecidableEq ι]
    {H f : Point d → ℝ} {g : ι → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : PolyC1 f)
    (s : Finset ι) (hg : ∀j∈s,PolyC1 (g j)) (v : Point d) :
    (∫x,adjointCoordinate H v f x*(∏j∈s,g j x) ∂gibbs H)=
      ∑j∈s,∫x,f x*directional v (g j) x*(∏k∈s.erase j,g k x) ∂gibbs H := by
  rw [adjointCoordinate_pairing hH ht hL hf (PolyC1.prod s hg) v,
    directional_prod s (fun j hj => (hg j hj).differentiable)]
  have he : (fun x => f x*(∑j∈s,(∏k∈s.erase j,g k x)*directional v (g j) x))=
      fun x => ∑j∈s,f x*directional v (g j) x*(∏k∈s.erase j,g k x) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply integral_finsetSum
  intro j hj
  have hp := PolyC1.prod (s.erase j) (fun k hk => hg k (Finset.mem_of_mem_erase hk))
  exact integrable_polynomial_gibbs hH.continuous ht
    ((hf.continuous.mul ((hg j hj).directional_continuous v)).mul hp.continuous)
    (Appell.HasGrowth.mul (Appell.HasGrowth.mul hf.growth ((hg j hj).derivative_growth v)) hp.growth)

theorem tensorAdjoint_product_pairing {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {H : Point d → ℝ} {V : ι → Point d → ℝ} {g : κ → Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hV : ∀i,PolyC1 (V i))
    (s : Finset κ) (hg : ∀j∈s,PolyC1 (g j)) (b : ι → Point d) :
    (∫x,tensorAdjoint H b V x*(∏j∈s,g j x) ∂gibbs H)=
      ∑i,∑j∈s,∫x,V i x*directional (b i) (g j) x*(∏k∈s.erase j,g k x) ∂gibbs H := by
  have hi (i : ι) : Integrable (fun x => adjointCoordinate H (b i) (V i) x*(∏j∈s,g j x)) (gibbs H) :=
    integrable_polynomial_gibbs hH.continuous ht
      ((adjointCoordinate_continuous hH (hV i) (b i)).mul (PolyC1.prod s hg).continuous)
      (Appell.HasGrowth.mul (adjointCoordinate_growth hL (hV i) (b i)) (PolyC1.prod s hg).growth)
  simp only [tensorAdjoint,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl (fun i _ => adjointCoordinate_product_pairing hH ht hL (hV i) s hg (b i))
end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma jet_directional {d : ℕ} {ι : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) (u : Point d) :
    JetCalculus.jet v l (directional u f)=directional u (JetCalculus.jet v l f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [JetCalculus.jet,ih]
    change directional (v i) (directional u (JetCalculus.jet v l f))=
      directional u (directional (v i) (JetCalculus.jet v l f))
    exact directional_commute (JetCalculus.smooth_jet hf v l) (v i) u

lemma jet_neg {d : ℕ} {ι : Type*} {f : Point d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) :
    JetCalculus.jet v l (fun x => -f x)=fun x => -JetCalculus.jet v l f x := by
  simpa only [neg_one_mul] using JetCalculus.jet_const_mul hf v l (-1)

theorem jet_adjointCoordinate {d : ℕ} {ι : Type*} [DecidableEq ι]
    {H f : Point d → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → Point d) (l : List ι) (hl : l.Nodup)
    (u : Point d) :
    JetCalculus.jet v l (adjointCoordinate H u f)=fun x =>
      adjointCoordinate H u (JetCalculus.jet v l f) x+
      ∑s∈l.toFinset.powerset.erase ∅,
        JetCalculus.jet v (l.filter (fun i => i∈s)) (directional u H) x*
        JetCalculus.jet v (l.filter (fun i => i∉s)) f x := by
  have hd := directional_smooth hf u
  have hs := directional_smooth hH u
  change JetCalculus.jet v l (fun x => -directional u f x+directional u H x*f x)=_
  rw [JetCalculus.jet_add hd.neg (hs.mul hf),jet_neg hd,jet_directional hf,
    JetCalculus.jet_mul hs hf v l hl]
  funext x
  dsimp only
  rw [←Finset.add_sum_erase _ _ (by simp : (∅:Finset ι)∈l.toFinset.powerset)]
  simp only [Finset.notMem_empty, decide_false, decide_not, Bool.not_false,
    List.filter_false, List.filter_true, JetCalculus.jet]
  simp only [adjointCoordinate]
  ring

theorem jet_tensorAdjoint {d : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {H : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hV : ∀i,ContDiff ℝ (⊤ : ℕ∞) (V i))
    (b : ι → Point d) (v : κ → Point d) (l : List κ) (hl : l.Nodup) :
    JetCalculus.jet v l (tensorAdjoint H b V)=fun x =>
      tensorAdjoint H b (fun i => JetCalculus.jet v l (V i)) x+
      ∑s∈l.toFinset.powerset.erase ∅,∑i,
        JetCalculus.jet v (l.filter (fun j => j∈s)) (directional (b i) H) x*
        JetCalculus.jet v (l.filter (fun j => j∉s)) (V i) x := by
  unfold tensorAdjoint
  rw [JetCalculus.jet_sum Finset.univ
    (fun i _ => adjointCoordinate_smooth hH (hV i) (b i))]
  simp_rw [jet_adjointCoordinate hH (hV _) v l hl]
  funext x
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

lemma commutator_term_count {ι : Type*} [DecidableEq ι] (l : List ι) (hl : l.Nodup) :
    (l.toFinset.powerset.erase ∅).card=2^l.length-1 := by
  rw [Finset.card_erase_of_mem (by simp),Finset.card_powerset,List.toFinset_card_of_nodup hl]
end LogConcaveSampling

end UpperProof
end
end
end

end OAI

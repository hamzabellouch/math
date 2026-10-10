import OAI.MathematicalPhysics.CriticalSK.HeatBath

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators Topology

open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators Topology
namespace CriticalSK


section

open Set Filter MeasureTheory

variable {n : ℕ} (W V : Disorder n)

lemma mean_square_center_identity (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => (f x-c)^2) = variance W f+(mean W f-c)^2 := by
  have hs : mean W (fun x => (f x-c)^2) = mean W (fun x => f x^2)-2*c*mean W f+c^2 := by
    have he : (fun x => (f x-c)^2) = (fun x => f x^2-(2*c)*f x+c^2) := by funext x; ring
    rw [he,mean_add,mean_sub,mean_const_mul,mean_const]
  have hv : variance W f = mean W (fun x => f x^2)-(mean W f)^2 := by
    unfold variance
    have he : (fun x => (f x-mean W f)^2) = (fun x => f x^2-(2*mean W f)*f x+(mean W f)^2) := by funext x; ring
    rw [he,mean_add,mean_sub,mean_const_mul,mean_const]
    ring
  rw [hs,hv]
  ring

lemma mean_least_squares (f : Spin n → ℝ) (c : ℝ) :
    variance W f ≤ mean W (fun x => (f x-c)^2) := by
  rw [mean_square_center_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma mean_density_upper {M : ℝ} (hM : ∀ x, gibbs W x ≤ M*gibbs V x)
    (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x) : mean W f ≤ M*mean V f := by
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  nlinarith [mul_le_mul_of_nonneg_right (hM x) (hf x)]

lemma variance_density_upper {M : ℝ} (hM : ∀ x, gibbs W x ≤ M*gibbs V x)
    (f : Spin n → ℝ) : variance W f ≤ M*variance V f :=
  (mean_least_squares W f (mean V f)).trans (mean_density_upper W V hM _ (fun _ => sq_nonneg _))

lemma dirichlet_density_lower {m : ℝ} (hm : 0 ≤ m) (hden : ∀ x, m*gibbs V x ≤ gibbs W x)
    (f : Spin n → ℝ) : m*dirichlet V f ≤ dirichlet W f := by
  unfold dirichlet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change m*mean V (fun x => (f x-siteAverage V i f x)^2) ≤ mean W (fun x => (f x-siteAverage W i f x)^2)
  have hh := siteAverage_least_squares V i f (siteAverage W i f) (fun x y h => (siteAverage_fiber_constant W i f h).symm)
  refine (mul_le_mul_of_nonneg_left hh hm).trans ?_
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  nlinarith [mul_le_mul_of_nonneg_right (hden x) (sq_nonneg (f x-siteAverage W i f x))]

lemma poincare_density_comparison {m M C : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hlower : ∀ x, m*gibbs V x ≤ gibbs W x) (hupper : ∀ x, gibbs W x ≤ M*gibbs V x)
    (hgap : ∀ f : Spin n → ℝ, variance V f ≤ C*dirichlet V f) (f : Spin n → ℝ) :
    variance W f ≤ (M/m*C)*dirichlet W f := by
  have hu := (variance_density_upper W V hupper f).trans (mul_le_mul_of_nonneg_left (hgap f) hM)
  have hl := dirichlet_density_lower W V hm.le hlower f
  have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hM hC)
  have he : (M/m*C)*dirichlet W f = (M*C*dirichlet W f)/m := by ring
  rw [he]
  apply (le_div_iff₀ hm).mpr
  have ht := mul_le_mul_of_nonneg_right hu hm.le
  nlinarith only [hh,ht]

lemma hamiltonian_scale (β : ℝ) (x : Spin n) : hamiltonian (β • W) x = β*hamiltonian W x := by
  simp only [hamiltonian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma gibbs_scale_ratio (β : ℝ) (x : Spin n) : gibbs W x =
    (partition (β • W)/partition W)*Real.exp ((1-β)*hamiltonian W x)*gibbs (β • W) x := by
  rw [gibbs,gibbs,hamiltonian_scale]
  have he : Real.exp ((1-β)*hamiltonian W x)*Real.exp (β*hamiltonian W x) = Real.exp (hamiltonian W x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp [ne_of_gt (partition_pos W),ne_of_gt (partition_pos (β • W))]
  nlinarith only [he]

lemma poincare_temperature_comparison {β R C : ℝ} (hβ : β ≤ 1) (hC : 0 ≤ C)
    (hH : ∀ x, |hamiltonian W x| ≤ R)
    (hgap : ∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f) (f : Spin n → ℝ) :
    variance W f ≤ (C*Real.exp (2*(1-β)*R))*dirichlet W f := by
  let z := partition (β • W)/partition W
  have hz : 0 < z := div_pos (partition_pos _) (partition_pos _)
  let m := z*Real.exp (-(1-β)*R)
  let M := z*Real.exp ((1-β)*R)
  have hm : 0 < m := mul_pos hz (Real.exp_pos _)
  have hM : 0 ≤ M := (mul_pos hz (Real.exp_pos _)).le
  have hl (x : Spin n) : m*gibbs (β • W) x ≤ gibbs W x := by
    rw [gibbs_scale_ratio W β x]
    apply mul_le_mul_of_nonneg_right _ (gibbs_nonneg _ _)
    apply mul_le_mul_of_nonneg_left _ hz.le
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (abs_le.mp (hH x)).1 (sub_nonneg.mpr hβ)
    nlinarith only [ht]
  have hu (x : Spin n) : gibbs W x ≤ M*gibbs (β • W) x := by
    rw [gibbs_scale_ratio W β x]
    apply mul_le_mul_of_nonneg_right _ (gibbs_nonneg _ _)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hH x)).2 (sub_nonneg.mpr hβ))) hz.le
  have hh := poincare_density_comparison W (β • W) hm hM hC hl hu hgap f
  have he : M/m*C = C*Real.exp (2*(1-β)*R) := by
    dsimp [M,m]
    rw [mul_div_mul_left _ _ hz.ne',← Real.exp_sub]
    rw [mul_comm]
    congr 2
    ring
  rwa [he] at hh

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma mean_kernel (K : Matrix (Spin n) (Spin n) ℝ)
    (hstat : ∀ y, ∑ x, gibbs W x*K x y = gibbs W y) (f : Spin n → ℝ) : mean W (K.mulVec f) = mean W f := by
  unfold mean Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← mul_assoc,← Finset.sum_mul,hstat]

lemma discreteKernel_quadratic_eq (f : Spin n → ℝ) :
    mean W (fun x => f x*(discreteKernel W).mulVec f x) =
      (n:ℝ)⁻¹*∑ i : Fin n, mean W (fun x => (siteAverage W i f x)^2) := by
  simp_rw [discreteKernel_average,mul_left_comm (f _),Finset.mul_sum,mean_sum,mean_const_mul,siteAverage_self_square]

lemma discreteKernel_square_le (hn : 0<n) (f : Spin n → ℝ) :
    mean W (fun x => ((discreteKernel W).mulVec f x)^2) ≤
      mean W (fun x => f x^2)-dirichlet W f/n := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hp (x : Spin n) : ((discreteKernel W).mulVec f x)^2 ≤ (n:ℝ)⁻¹*∑ i : Fin n, (siteAverage W i f x)^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _i : Fin n => (1:ℝ)) (fun i => siteAverage W i f x)
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    rw [discreteKernel_average,← div_eq_inv_mul,div_pow,← div_eq_inv_mul]
    apply (div_le_div_iff₀ (sq_pos_of_pos hnpos) hnpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hh hnpos.le]
  have hm := mean_mono W hp
  rw [mean_const_mul,mean_sum,← discreteKernel_quadratic_eq] at hm
  have hd := dirichlet_discrete W hn f
  have he : mean W (fun x => f x*(f x-(discreteKernel W).mulVec f x)) =
      mean W (fun x => f x^2)-mean W (fun x => f x*(discreteKernel W).mulVec f x) := by
    rw [← mean_sub]
    congr 1
    funext x
    ring
  rw [he] at hd
  linarith

lemma gap_factor_nonneg (hn : 0<n) {C : ℝ} (hC : 1≤C) : 0 ≤ 1-1/((n:ℝ)*C) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hnc : 1≤(n:ℝ)*C := le_trans hC (le_mul_of_one_le_left (le_trans zero_le_one hC) hn1)
  have hpos : 0<(n:ℝ)*C := lt_of_lt_of_le zero_lt_one hnc
  exact sub_nonneg.mpr ((div_le_one hpos).mpr hnc)

lemma gap_square_step (hn : 0<n) {C : ℝ} (hC : 0<C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (f : Spin n → ℝ) (hf : mean W f=0) :
    mean W (fun x => ((discreteKernel W).mulVec f x)^2) ≤
      (1-1/((n:ℝ)*C))*mean W (fun x => f x^2) := by
  have hg := hgap f
  simp only [variance,hf,sub_zero] at hg
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hd : mean W (fun x => f x^2)/((n:ℝ)*C) ≤ dirichlet W f/n := by
    apply (div_le_div_iff₀ (mul_pos hnpos hC) hnpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hg hnpos.le]
  have hs := discreteKernel_square_le W hn f
  have he : (1-1/((n:ℝ)*C))*mean W (fun x => f x^2) = mean W (fun x => f x^2)-mean W (fun x => f x^2)/((n:ℝ)*C) := by ring
  rw [he]
  linarith

lemma gap_square_pow (hn : 0<n) {C : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (f : Spin n → ℝ) (hf : mean W f=0) (k : ℕ) :
    mean W (fun x => ((discreteKernel W^k).mulVec f x)^2) ≤
      (1-1/((n:ℝ)*C))^k*mean W (fun x => f x^2) := by
  induction k with
  | zero => simp only [pow_zero,Matrix.one_mulVec,one_mul,le_refl]
  | succ k ih =>
    have hzero : mean W ((discreteKernel W^k).mulVec f)=0 := by rw [mean_kernel W _ (kernel_pow_stationary (discreteKernel_stationary W hn) k),hf]
    have hs := gap_square_step W hn (lt_of_lt_of_le zero_lt_one hC) hgap _ hzero
    rw [pow_succ',← Matrix.mulVec_mulVec]
    refine hs.trans ?_
    rw [pow_succ']
    exact (mul_le_mul_of_nonneg_left ih (gap_factor_nonneg hn hC)).trans_eq (mul_assoc _ _ _).symm

lemma gap_square_exponential (hn : 0<n) {C : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (f : Spin n → ℝ) (hf : mean W f=0) (k : ℕ) :
    mean W (fun x => ((discreteKernel W^k).mulVec f x)^2) ≤
      Real.exp (-(k:ℝ)/((n:ℝ)*C))*mean W (fun x => f x^2) := by
  refine (gap_square_pow W hn hC hgap f hf k).trans ?_
  apply mul_le_mul_of_nonneg_right _ (mean_nonneg W (fun _ => sq_nonneg _))
  have he : 1-1/((n:ℝ)*C) ≤ Real.exp (-1/((n:ℝ)*C)) := by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-1/((n:ℝ)*C))
  have hh := pow_le_pow_left₀ (gap_factor_nonneg hn hC) he k
  rw [← Real.exp_nat_mul] at hh
  convert hh using 1
  congr 1
  ring

end


section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma kernel_pow_reversible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℝ} {μ : ι → ℝ} (h : ∀ x y, μ x*K x y=μ y*K y x)
    (k : ℕ) (x y : ι) : μ x*(K^k) x y=μ y*(K^k) y x := by
  induction k generalizing x y with
  | zero => simp only [pow_zero,Matrix.one_apply]; split_ifs with he <;> simp_all
  | succ k ih =>
    rw [pow_succ,Matrix.mul_apply,Finset.mul_sum]
    calc
      _ = ∑ z, μ y*K y z*(K^k) z x := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← mul_assoc,ih,mul_assoc,mul_left_comm, h z y]
        ring
      _ = μ y*(K^(k+1)) y x := by rw [pow_succ',Matrix.mul_apply,Finset.mul_sum]; ring_nf

lemma mean_abs_square_le (f : Spin n → ℝ) : (mean W (fun x => |f x|))^2 ≤ mean W (fun x => f x^2) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => Real.sqrt (gibbs W x)) (fun x => Real.sqrt (gibbs W x)*|f x|)
  simp only [mul_pow,Real.sq_sqrt (gibbs_nonneg W _),sq_abs,gibbs_sum,one_mul] at hh
  have he : (∑ x : Spin n, Real.sqrt (gibbs W x)*(Real.sqrt (gibbs W x)*|f x|)) = mean W (fun x => |f x|) := by
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc,Real.mul_self_sqrt (gibbs_nonneg W _)]
  rw [he] at hh
  exact hh

def centeredPointDensity (x : Spin n) : Spin n → ℝ := fun y => (if y=x then (gibbs W x)⁻¹ else 0)-1

lemma centeredPointDensity_mean (x : Spin n) : mean W (centeredPointDensity W x)=0 := by
  change mean W (fun y => (if y=x then (gibbs W x)⁻¹ else 0)-1)=0
  rw [mean_sub,mean_const]
  unfold mean
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [mul_inv_cancel₀ (gibbs_pos W x).ne',sub_self]

lemma centeredPointDensity_square (x : Spin n) : mean W (fun y => centeredPointDensity W x y ^ 2) = (gibbs W x)⁻¹-1 := by
  have hid (y : Spin n) : centeredPointDensity W x y ^2 = (if y=x then (gibbs W x)⁻¹^2-2*(gibbs W x)⁻¹ else 0)+1 := by
    unfold centeredPointDensity
    split_ifs <;> ring
  simp_rw [hid]
  rw [mean_add,mean_const]
  unfold mean
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp [(gibbs_pos W x).ne']
  ring

lemma centeredPointDensity_kernel (hn : 0<n) (x y : Spin n) (k : ℕ) :
    (discreteKernel W^k).mulVec (centeredPointDensity W x) y =
      (discreteKernel W^k) x y/gibbs W y-1 := by
  have hrev := kernel_pow_reversible (discreteKernel_reversible W) k y x
  unfold Matrix.mulVec dotProduct centeredPointDensity
  simp only [mul_sub,Finset.sum_sub_distrib,mul_one,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [kernel_pow_sum (discreteKernel_sum W hn)]
  have hx := (gibbs_pos W x).ne'
  have hy := (gibbs_pos W y).ne'
  field_simp
  nlinarith only [hrev]

lemma discreteDistance_mean_density (hn : 0<n) (x : Spin n) (k : ℕ) :
    discreteDistance W k x = (1/2:ℝ)*mean W (fun y => |(discreteKernel W^k).mulVec (centeredPointDensity W x) y|) := by
  unfold discreteDistance totalVariation mean
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  change |(discreteKernel W^k) x y-gibbs W y|=gibbs W y*|(discreteKernel W^k).mulVec (centeredPointDensity W x) y|
  rw [centeredPointDensity_kernel W hn]
  symm
  calc
    _ = |gibbs W y| *|(discreteKernel W^k) x y/gibbs W y-1| := by rw [abs_of_nonneg (gibbs_nonneg W y)]
    _ = _ := by
      rw [← abs_mul]
      congr 1
      field_simp [(gibbs_pos W y).ne']

lemma discreteDistance_square_gap (hn : 0<n) {C : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f) (x : Spin n) (k : ℕ) :
    (discreteDistance W k x)^2 ≤ Real.exp (-(k:ℝ)/((n:ℝ)*C))/(4*gibbs W x) := by
  rw [discreteDistance_mean_density W hn,mul_pow]
  have hh := (mean_abs_square_le W ((discreteKernel W^k).mulVec (centeredPointDensity W x))).trans
    (gap_square_exponential W hn hC hgap _ (centeredPointDensity_mean W x) k)
  rw [centeredPointDensity_square] at hh
  have ht := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ (1/2)^2)
  have he := Real.exp_nonneg (-(k:ℝ)/((n:ℝ)*C))
  have hid : Real.exp (-(k:ℝ)/((n:ℝ)*C))/(4*gibbs W x) = (1/2:ℝ)^2*(Real.exp (-(k:ℝ)/((n:ℝ)*C))*(gibbs W x)⁻¹) := by ring
  rw [hid]
  nlinarith only [ht,he]

lemma discreteDistance_gap_bound (hn : 0<n) {C A : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A) ≤ gibbs W x) (x : Spin n) (k : ℕ) :
    discreteDistance W k x ≤ Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2 := by
  have hs := discreteDistance_square_gap W hn hC hgap x k
  have he : Real.exp (-(k:ℝ)/((n:ℝ)*C))/(4*gibbs W x) ≤
      (Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2)^2 := by
    have hμ : 0<gibbs W x := gibbs_pos W x
    have hh := div_le_div_of_nonneg_left (Real.exp_nonneg (-(k:ℝ)/((n:ℝ)*C))) (by positivity : 0<4*Real.exp (-A)) (mul_le_mul_of_nonneg_left (hmin x) (by norm_num : (0:ℝ)≤4))
    refine hh.trans_eq ?_
    rw [div_pow,← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num]
    rw [show (2:ℝ)*((A-(k:ℝ)/((n:ℝ)*C))/2)=A-(k:ℝ)/((n:ℝ)*C) by ring]
    rw [show 4*Real.exp (-A)=Real.exp (-A)*4 by ring,div_mul_eq_div_div,← Real.exp_sub]
    congr 1
    congr 1
    ring
  have hnonneg : 0≤Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2 := by positivity
  nlinarith [hs.trans he,sq_nonneg (discreteDistance W k x+Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2)/2)]

end

section

open Set Filter MeasureTheory

lemma poisson_generating_hasSum (a r : ℝ) :
    HasSum (fun k : ℕ => (Real.exp (-a)*a^k/k.factorial)*r^k) (Real.exp (a*(r-1))) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a*r)).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ,← Real.exp_add,show -a+a*r=a*(r-1) by ring] at h
  apply h.congr_fun
  intro k
  simp only [smul_eq_mul,mul_pow]
  ring

lemma finite_l1_series_bound {ι : Type*} [Fintype ι]
    (F : ℕ → ι → ℝ) (z : ι → ℝ) (g : ℕ → ℝ) (B : ℝ)
    (hf : ∀ y, HasSum (fun k => F k y) (z y)) (hg : HasSum g B)
    (hb : ∀ k, (∑ y, |F k y|) ≤ g k) : (∑ y, |z y|) ≤ B := by
  classical
  have ht : Summable (fun k => ∑ y, |F k y|) :=
    Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hb hg.summable
  have hs (y : ι) : Summable (fun k => |F k y|) := by
    have hc (k : ℕ) : |F k y| ≤ ∑ i : ι, |F k i| :=
      Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => abs_nonneg (F k i)) (Finset.mem_univ y)
    exact Summable.of_nonneg_of_le (fun k => abs_nonneg (F k y)) hc ht
  have he (y : ι) : |z y| ≤ ∑' k, |F k y| :=
    (hf y).norm_le_of_bounded (hs y).hasSum (fun _ => le_rfl)
  calc
    _ ≤ ∑ y, ∑' k, |F k y| := Finset.sum_le_sum (fun y _ => he y)
    _ = ∑' k, ∑ y, |F k y| := (Summable.tsum_finsetSum (fun y _ => hs y)).symm
    _ ≤ B := hasSum_le hb ht.hasSum hg

lemma poisson_l1_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (μ : ι → ℝ) (a : ℝ) (ha : 0≤a) (B r : ℝ) (x : ι)
    (hbound : ∀ k : ℕ, (∑ y, |(K^k) x y-μ y|) ≤ B*r^k) :
    (∑ y, |NormedSpace.exp (a • (K-1)) x y-μ y|) ≤ B*Real.exp (a*(r-1)) := by
  let c : ℕ → ℝ := fun k => Real.exp (-a)*a^k/k.factorial
  have hc (k : ℕ) : 0≤c k := poisson_coeff_nonneg a ha k
  have hgen : HasSum (fun k : ℕ => c k*(B*r^k)) (B*Real.exp (a*(r-1))) := by
    apply ((poisson_generating_hasSum a r).mul_left B).congr_fun
    intro k
    dsimp [c]
    ring
  have hf (y : ι) : HasSum (fun k => c k*((K^k) x y-μ y)) (NormedSpace.exp (a • (K-1)) x y-μ y) := by
    have hh := (matrix_poisson_hasSum K a x y).sub ((poisson_coeff_hasSum a).mul_right (μ y))
    rw [one_mul] at hh
    apply hh.congr_fun
    intro k
    dsimp [c]
    ring
  apply finite_l1_series_bound _ _ _ _ hf hgen
  intro k
  simp only [abs_mul,abs_of_nonneg (hc k),← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hbound k) (hc k)

lemma exp_neg_linear_bound {u : ℝ} (hu : 0≤u) (hu1 : u≤1) : Real.exp (-u) ≤ 1-u/2 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (Real.exp_nonneg (-u))
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  have hp : 0<1+u := by linarith
  have ht : 1≤(1-u/2)*(1+u) := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  apply (mul_le_mul_iff_of_pos_right hp).mp
  nlinarith only [hh,ht]

variable {n : ℕ} (W : Disorder n)

lemma continuousDistance_gap_bound (hn : 0<n) {C A : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A) ≤ gibbs W x) {t : ℝ} (ht : 0≤t) (x : Spin n) :
    continuousDistance W t x ≤ Real.exp (A/2-t/(4*C))/2 := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hCpos : 0<C := lt_of_lt_of_le zero_lt_one hC
  let r := Real.exp (-1/(2*(n:ℝ)*C))
  have hdis (k : ℕ) : (∑ y, |(discreteKernel W^k) x y-gibbs W y|) ≤ Real.exp (A/2)*r^k := by
    have hh := discreteDistance_gap_bound W hn hC hgap hmin x k
    have he : Real.exp ((A-(k:ℝ)/((n:ℝ)*C))/2) = Real.exp (A/2)*r^k := by
      dsimp [r]
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    unfold discreteDistance totalVariation at hh
    linarith only [hh]
  have hh := poisson_l1_bound (discreteKernel W) (gibbs W) ((n:ℝ)*t) (mul_nonneg hnpos.le ht) (Real.exp (A/2)) r x hdis
  rw [← continuousKernel_poisson W hn t] at hh
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hnc : 1≤(n:ℝ)*C := le_trans hC (le_mul_of_one_le_left hCpos.le hn1)
  have hu : 0≤1/(2*(n:ℝ)*C) := by positivity
  have hu1 : 1/(2*(n:ℝ)*C)≤1 := by
    apply (div_le_one (by positivity : 0<2*(n:ℝ)*C)).mpr
    nlinarith only [hnc]
  have hr : r≤1-1/(2*(n:ℝ)*C)/2 := by simpa only [r,neg_div] using exp_neg_linear_bound hu hu1
  have hrate : (n:ℝ)*t*(r-1) ≤ -t/(4*C) := by
    have hs := mul_le_mul_of_nonneg_left (sub_le_sub_right hr 1) (mul_nonneg hnpos.le ht)
    have he : (n:ℝ)*t*((1-1/(2*(n:ℝ)*C)/2)-1) = -t/(4*C) := by field_simp; ring
    rwa [he] at hs
  have hex := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) (Real.exp_nonneg (A/2))
  have hfinal : Real.exp (A/2)*Real.exp (-t/(4*C)) = Real.exp (A/2-t/(4*C)) := by rw [← Real.exp_add]; congr 1; ring
  rw [hfinal] at hex
  unfold continuousDistance totalVariation
  linarith only [hh,hex]

end

open Set Filter MeasureTheory

lemma exp_neg_two_le_half : Real.exp (-2) ≤ (1/2:ℝ) := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp 2) (Real.exp_nonneg (-2))
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  linarith [Real.exp_nonneg (-2)]

variable {n : ℕ} (W : Disorder n)

lemma gibbs_lower_of_energy_bound {R : ℝ} (hH : ∀ x, |hamiltonian W x|≤R) (x : Spin n) :
    Real.exp (-(2*R+(n:ℝ))) ≤ gibbs W x := by
  have hcard : (Fintype.card (Spin n):ℝ) ≤ Real.exp (n:ℝ) := by
    have he : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) he n
    rw [← Real.exp_nat_mul,mul_one] at hh
    simpa only [Spin,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hz : partition W ≤ Real.exp (R+(n:ℝ)) := by
    calc
      _ ≤ ∑ _x : Spin n, Real.exp R := Finset.sum_le_sum (fun x _ => Real.exp_le_exp.mpr (abs_le.mp (hH x)).2)
      _ = (Fintype.card (Spin n):ℝ)*Real.exp R := by simp
      _ ≤ Real.exp (n:ℝ)*Real.exp R := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (R+(n:ℝ)) := by rw [← Real.exp_add,add_comm]
  unfold gibbs
  apply (le_div_iff₀ (partition_pos W)).mpr
  calc
    _ ≤ Real.exp (-(2*R+(n:ℝ)))*Real.exp (R+(n:ℝ)) := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (hamiltonian W x) := Real.exp_le_exp.mpr (abs_le.mp (hH x)).1

lemma continuousMixingTime_le_of_distance {t : ℝ} (ht : 0≤t)
    (hd : ∀ x, continuousDistance W t x ≤ 1/4) : continuousMixingTime W ≤ t := by
  apply csInf_le (show BddBelow {s : ℝ | 0 ≤ s ∧ ∀ x, continuousDistance W s x≤1/4} from ⟨0,fun _ hs => hs.1⟩)
  exact ⟨ht,hd⟩

lemma discreteMixingTime_le_of_distance {k : ℕ}
    (hd : ∀ x, discreteDistance W k x ≤ 1/4) : discreteMixingTime W ≤ k := Nat.sInf_le hd

lemma finite_continuous_gap_mixing (hn : 0<n) {C A : ℝ} (hC : 1≤C) (hA : 0≤A)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A)≤gibbs W x) :
    continuousMixingTime W ≤ 4*C*(A+4) := by
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  have ht : 0≤4*C*(A+4) := by positivity
  apply continuousMixingTime_le_of_distance W ht
  intro x
  have hh := continuousDistance_gap_bound W hn hC hgap hmin ht x
  have he : A/2-(4*C*(A+4))/(4*C) ≤ -2 := by
    field_simp
    nlinarith
  have hb := Real.exp_le_exp.mpr he
  have hexp := exp_neg_two_le_half
  linarith

lemma finite_discrete_gap_mixing (hn : 0<n) {C A : ℝ} (hC : 1≤C)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hmin : ∀ x, Real.exp (-A)≤gibbs W x) {k : ℕ} (hk : (n:ℝ)*C*(A+4)≤k) :
    discreteMixingTime W ≤ k := by
  have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  apply discreteMixingTime_le_of_distance W
  intro x
  have hh := discreteDistance_gap_bound W hn hC hgap hmin x k
  have he : (A-(k:ℝ)/((n:ℝ)*C))/2 ≤ -2 := by
    have hq : A+4 ≤ (k:ℝ)/((n:ℝ)*C) := (le_div_iff₀ (mul_pos hnpos hCp)).mpr (by nlinarith only [hk])
    linarith
  have hb := Real.exp_le_exp.mpr he
  linarith [exp_neg_two_le_half]

lemma finite_gap_mixing_bounds (hn : 0<n) {C R : ℝ} (hC : 1≤C) (hR : 0≤R)
    (hgap : ∀ f : Spin n → ℝ, variance W f ≤ C*dirichlet W f)
    (hH : ∀ x, |hamiltonian W x|≤R) :
    continuousMixingTime W ≤ 4*C*(2*R+n+4) ∧
    (discreteMixingTime W:ℝ) ≤ (n:ℝ)*C*(2*R+n+4)+1 := by
  constructor
  · exact finite_continuous_gap_mixing W hn hC (by positivity) hgap (gibbs_lower_of_energy_bound W hH)
  · let a := (n:ℝ)*C*(2*R+n+4)
    have ha : 0≤a := by dsimp [a]; positivity
    have hk : a≤(⌈a⌉₊:ℝ) := Nat.le_ceil a
    have hm := finite_discrete_gap_mixing W hn hC hgap (gibbs_lower_of_energy_bound W hH) hk
    exact (Nat.cast_le.mpr hm).trans (Nat.ceil_lt_add_one ha).le

end CriticalSK

end

end OAI

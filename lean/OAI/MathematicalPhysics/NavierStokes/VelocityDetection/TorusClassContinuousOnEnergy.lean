import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstTotalForce
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TorusClass

namespace OAI

noncomputable section
namespace VelocityDetection.TorusClass
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators

theorem continuousOn_energy {e : ℝ → Space → Vect} {T : ℝ}
    (hc : ∀ i, ContinuousOn (fun q : ℝ × Space => e q.1 q.2 i) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun t => energy (e t)) (Icc 0 T) :=
  integral_continuous (continuousOn_finsetSum _ (fun i _ => (hc i).pow 2))

theorem energy_hasDerivAt {e de : ℝ → Space → Vect} {T t : ℝ}
    (hc : ∀ i, ContinuousOn (fun q : ℝ × Space => e q.1 q.2 i) (Icc 0 T ×ˢ univ))
    (hdc : ∀ i, ContinuousOn (fun q : ℝ × Space => de q.1 q.2 i) (Icc 0 T ×ˢ univ))
    (hd : ∀ s ∈ Icc 0 T, ∀ x i,
      HasDerivWithinAt (fun r => e r x i) (de s x i) (Icc 0 T) s)
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun t => energy (e t)) (2*work (e t) (de t)) t := by
  have hder (s : ℝ) (hs : s ∈ Icc 0 T) (x : Space) :
      HasDerivWithinAt (fun r => ∑ i, (e r x i)^2)
        (2 * ∑ i, e s x i * de s x i) (Icc 0 T) s := by
    have hh := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ => (hd s hs x i).pow 2)
    convert hh using 1 <;> try rfl
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Finset.mul_sum, mul_assoc]
  have hh := integral_hasDerivAt (f := fun s x => ∑ i, (e s x i)^2)
    (df := fun s x => 2 * ∑ i, e s x i * de s x i)
    (continuousOn_finsetSum _ (fun i _ => (hc i).pow 2))
    ((continuousOn_finsetSum _ (fun i _ => (hc i).mul (hdc i))).const_mul 2) hder ht
  simpa only [energy,work,integral_const_mul] using hh

abbrev L2Space := Lp ℝ 2 measure

theorem energy_eq_L2 (e : Space → Vect) (E : Fin 3 → L2Space)
    (hE : ∀ i, (fun x => E i x) =ᵐ[measure] (fun x => e x i)) :
    energy e = ∑ i, ‖E i‖^2 := by
  have h2 (i : Fin 3) : MemLp (fun x => e x i) 2 measure := (memLp_congr_ae (hE i)).mp (Lp.memLp (E i))
  rw [energy, integral_finsetSum _ (fun i _ => integrable_sq_L2 (h2 i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hE i] with x hx
  simp [hx, sq]

theorem periodic_eq_zero_of_ae {f : Space → ℝ} (hf : Continuous f) (hp : periodic f)
    (hz : f =ᵐ[measure] 0) : ∀ x, f x = 0 := by
  have hclosure : Icc (0 : Space) 1 ⊆ closure (interior (Icc (0 : Space) 1)) := by
    have hcube : Icc (0 : Space) 1 = univ.pi (fun _ : Fin 3 => Icc (0:ℝ) 1) := by
      ext x
      simp only [mem_Icc,Pi.le_def,Pi.zero_apply,Pi.one_apply,mem_univ_pi]
      exact forall_and.symm
    rw [hcube,interior_pi_set (finite_univ),closure_pi_set]
    simp only [closure_interior_Icc (by norm_num : (0:ℝ) ≠ 1)]
    exact Subset.rfl
  have hzero := Measure.eqOn_of_ae_eq hz hf.continuousOn continuousOn_const hclosure
  intro X
  let Y : Space := fun i => Int.fract (X i)
  have hY : Y ∈ Icc (0 : Space) 1 :=
    ⟨fun i => Int.fract_nonneg _,fun i => (Int.fract_lt_one _).le⟩
  have hXY : PeriodicSpace.cover X = PeriodicSpace.cover Y := by
    apply Periodization.cover_eq_iff.mpr
    refine ⟨fun i => ⌊X i⌋,?_⟩
    ext i
    exact (sub_add_cancel _ _).symm
  exact (hp hXY).trans (hzero hY)

theorem eq_zero_of_energy_zero {e : Space → Vect} (he : ∀ i, Continuous (fun x => e x i))
    (hp : ∀ i, periodic (fun x => e x i)) (h2 : ∀ i, MemLp (fun x => e x i) 2 measure)
    (hz : energy e = 0) : ∀ x, e x = 0 := by
  let E : Fin 3 → L2Space := fun i => (h2 i).toLp (fun x => e x i)
  have hE (i : Fin 3) : (fun x => E i x) =ᵐ[measure] (fun x => e x i) := (h2 i).coeFn_toLp
  have hsum : ∑ i, ‖E i‖^2 = 0 := (energy_eq_L2 e E hE).symm.trans hz
  have hnorm (i : Fin 3) : E i = 0 := by
    have hsq := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖E j‖)).mp hsum i (Finset.mem_univ i)
    apply norm_eq_zero.mp
    nlinarith only [hsq, norm_nonneg (E i)]
  intro x
  ext i
  exact periodic_eq_zero_of_ae (he i) (hp i)
    ((hE i).symm.trans (by simpa only [hnorm i] using Lp.coeFn_zero ℝ 2 measure)) x

theorem difference_zero
    {e de v U : ℝ → Space → Vect} {q : ℝ → Space → ℝ}
    {ν B T : ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (he : ∀ t ∈ Icc 0 T, SliceH2 (e t))
    (hv : ∀ t ∈ Icc 0 T, ∀ i, ContDiff ℝ 1 (fun x => v t x i))
    (hvp : ∀ t ∈ Icc 0 T, ∀ i, periodic (fun x => v t x i))
    (hU : ∀ t ∈ Icc 0 T, ∀ i, ContDiff ℝ 1 (fun x => U t x i))
    (hq : ∀ t ∈ Icc 0 T, PressureH1 (q t))
    (hvb : ∀ t ∈ Icc 0 T, ∀ x i, |v t x i| ≤ B)
    (hDvb : ∀ t ∈ Icc 0 T, ∀ x i, |D i (fun y => v t y i) x| ≤ B)
    (hDUb : ∀ t ∈ Icc 0 T, ∀ x i k, |D k (fun y => U t y i) x| ≤ B)
    (hvdiv : ∀ t ∈ Icc 0 T, ∀ x, div (v t) x = 0)
    (hediv : ∀ t ∈ Icc 0 T, ∀ x, div (e t) x = 0)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x i,
      de t x i + (∑ k, v t x k * D k (fun y => e t y i) x) +
        (∑ k, e t x k * D k (fun y => U t y i) x) =
        -D i (q t) x + ν * lap (fun y => e t y i) x)
    (hc : ∀ i, ContinuousOn (fun r : ℝ × Space => e r.1 r.2 i) (Icc 0 T ×ˢ univ))
    (hdc : ∀ i, ContinuousOn (fun r : ℝ × Space => de r.1 r.2 i) (Icc 0 T ×ˢ univ))
    (hder : ∀ t ∈ Icc 0 T, ∀ x i,
      HasDerivWithinAt (fun s => e s x i) (de t x i) (Icc 0 T) t)
    (h0 : ∀ x, e 0 x = 0) : ∀ t ∈ Icc 0 T, ∀ x, e t x = 0 := by
  have hderF (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun t => energy (e t)) (2 * work (e t) (de t)) t :=
    energy_hasDerivAt hc hdc hder ht
  have hb (t : ℝ) (ht : t ∈ Ioo 0 T) : 2 * work (e t) (de t) ≤ (6*B) * energy (e t) := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have hde (i : Fin 3) : MemLp (fun x => de t x i) 2 measure :=
      memLp_continuous (continuous_slice (f := fun t x => de t x i) (hdc i) ht') 2
    have hh := difference_energy_inequality hν hB (he t ht') hde (hv t ht') (hvp t ht')
      (hU t ht') (hq t ht') (hvb t ht') (hDvb t ht') (hDUb t ht') (hvdiv t ht')
      (hediv t ht') (hpde t ht')
    nlinarith only [hh]
  have hz := Cylinder.energy_gronwall_zero hT (continuousOn_energy hc) hderF hb
    (show energy (e 0) = 0 by simp [energy, h0]) (fun t _ => energy_nonneg (e t))
  intro t ht
  exact eq_zero_of_energy_zero (fun i => ((he t ht).smooth i).continuous) (he t ht).per
    (he t ht).square_integrable (hz t ht)

theorem lap_sub {f g : Space → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : Space) : lap (fun y => f y - g y) x = lap f x - lap g x := by
  have hd : ∀ i, D i (fun y => f y - g y) = fun y => D i f y - D i g y :=
    fun i => funext (D_sub (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)) i)
  simp only [lap, hd, D_sub ((contDiff_D hf _).differentiable (by norm_num))
    ((contDiff_D hg _).differentiable (by norm_num)), Finset.sum_sub_distrib]

theorem SliceH2.sub {v U : Space → Vect} (hv : SliceH2 v) (hU : SliceH2 U) :
    SliceH2 (fun x i => v x i - U x i) := by
  have hd (i k : Fin 3) : D k (fun x => v x i - U x i) =
      fun x => D k (fun y => v y i) x - D k (fun y => U y i) x :=
    funext (D_sub ((hv.smooth i).differentiable (by norm_num))
      ((hU.smooth i).differentiable (by norm_num)) k)
  refine ⟨fun i => (hv.smooth i).sub (hU.smooth i),
    fun i => periodic_sub (hv.per i) (hU.per i),
    fun i => (hv.square_integrable i).sub (hU.square_integrable i), ?_, ?_⟩
  · intro i k
    rw [hd]
    exact (hv.derivative_square_integrable i k).sub (hU.derivative_square_integrable i k)
  · intro i k l
    rw [hd]
    change MemLp (fun x => D l (fun y => D k (fun z => v z i) y - D k (fun z => U z i) y) x) 2 measure
    simp_rw [D_sub ((contDiff_D (hv.smooth i) k).differentiable (by norm_num))
      ((contDiff_D (hU.smooth i) k).differentiable (by norm_num))]
    exact (hv.second_square_integrable i k l).sub (hU.second_square_integrable i k l)

theorem PressureH1.sub {p q : Space → ℝ} (hp : PressureH1 p) (hq : PressureH1 q) :
    PressureH1 (fun x => p x - q x) := by
  refine ⟨hp.smooth.sub hq.smooth, periodic_sub hp.per hq.per,
    hp.square_integrable.sub hq.square_integrable, ?_⟩
  intro k
  change MemLp (fun x => D k (fun y => p y - q y) x) 2 measure
  simp_rw [D_sub (hp.smooth.differentiable (by norm_num))
    (hq.smooth.differentiable (by norm_num))]
  exact (hp.derivative_square_integrable k).sub (hq.derivative_square_integrable k)

theorem fderiv_eq_zero_of_D_eq_zero {q : Space → ℝ} {x : Space}
    (hq : ∀ i, D i q x = 0) : fderiv ℝ q x = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  have hy : y = y 0 • frame 0 + y 1 • frame 1 + y 2 • frame 2 := by
    ext i
    fin_cases i <;> simp [frame]
  change fderiv ℝ q x y = 0
  rw [hy]
  dsimp only [D] at hq
  simp only [map_add, map_smul, hq, smul_zero, add_zero]

theorem pressure_zero_of_gradient_zero {q : Space → ℝ}
    (hq : Differentiable ℝ q) (hmean : (∫ x, q x ∂measure) = 0)
    (hD : ∀ x i, D i q x = 0) : ∀ x, q x = 0 := by
  have hconst : q = fun _ => q 0 := funext fun x =>
    is_const_of_fderiv_eq_zero hq (fun x => fderiv_eq_zero_of_D_eq_zero (hD x)) x 0
  rw [hconst] at hmean
  have h0 : q 0 = 0 := by simpa only [integral_const,probReal_univ,one_smul] using hmean
  intro x
  rw [hconst,h0]

structure EnergyRegularOn (u du : ℝ → Space → Vect) (p : ℝ → Space → ℝ)
    (T : ℝ) : Prop where
  space : ∀ t ∈ Icc 0 T, SliceH2 (u t)
  pressure : ∀ t ∈ Icc 0 T, PressureH1 (p t)
  pressure_mean : ∀ t ∈ Icc 0 T, (∫ x, p t x ∂measure) = 0
  pointwise_time : ∀ t ∈ Icc 0 T, ∀ x i,
    HasDerivWithinAt (fun s => u s x i) (du t x i) (Icc 0 T) t
  joint : ∀ i, ContinuousOn (fun y : ℝ × Space => u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  derivative_joint : ∀ i, ContinuousOn (fun y : ℝ × Space => du y.1 y.2 i) (Icc 0 T ×ˢ univ)
  bounded : ∃ B : ℝ, 0 ≤ B ∧
    (∀ t ∈ Icc 0 T, ∀ x i, |u t x i| ≤ B) ∧
    (∀ t ∈ Icc 0 T, ∀ x i k, |D k (fun y => u t y i) x| ≤ B)

def solvesOn (ν : ℝ) (f u du : ℝ → Space → Vect) (p : ℝ → Space → ℝ)
    (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, ∀ x, div (u t) x = 0) ∧
  (∀ t ∈ Icc 0 T, ∀ x i,
    du t x i + (∑ k, u t x k * D k (fun y => u t y i) x) =
      -D i (p t) x + ν * lap (fun y => u t y i) x + f t x i)

theorem unique_velocity_and_pressure
    {u du v dv f : ℝ → Space → Vect} {p q : ℝ → Space → ℝ} {T ν : ℝ}
    (hT : 0 < T) (hν : 0 ≤ ν)
    (hu : EnergyRegularOn u du p T) (hv : EnergyRegularOn v dv q T)
    (hupde : solvesOn ν f u du p T) (hvpde : solvesOn ν f v dv q T)
    (h0 : ∀ x, v 0 x = u 0 x) :
    (∀ t ∈ Icc 0 T, ∀ x, v t x = u t x) ∧
    (∀ t ∈ Icc 0 T, ∀ x, q t x = p t x) := by
  rcases hu.bounded with ⟨BU, hBU, hUb, hDUb⟩
  rcases hv.bounded with ⟨BV, hBV, hVb, hDVb⟩
  let e : ℝ → Space → Vect := fun t x i => v t x i - u t x i
  let de : ℝ → Space → Vect := fun t x i => dv t x i - du t x i
  let r : ℝ → Space → ℝ := fun t x => q t x - p t x
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) (i k : Fin 3) :
      D k (fun y => e t y i) x =
        D k (fun y => v t y i) x - D k (fun y => u t y i) x :=
    D_sub ((hv.space t ht).smooth i |>.differentiable (by norm_num))
      ((hu.space t ht).smooth i |>.differentiable (by norm_num)) k x
  have hediv (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) : div (e t) x = 0 := by
    simp only [div, hd t ht, Finset.sum_sub_distrib]
    change div (v t) x - div (u t) x = 0
    rw [hvpde.1 t ht, hupde.1 t ht, sub_self]
  have hePDE (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) (i : Fin 3) :
      de t x i + (∑ k, v t x k * D k (fun y => e t y i) x) +
        (∑ k, e t x k * D k (fun y => u t y i) x) =
        -D i (r t) x + ν * lap (fun y => e t y i) x := by
    have huv := hupde.2 t ht x i
    have hvv := hvpde.2 t ht x i
    simp only [hd t ht]
    change dv t x i - du t x i +
      (∑ k, v t x k * (D k (fun y => v t y i) x - D k (fun y => u t y i) x)) +
      (∑ k, (v t x k - u t x k) * D k (fun y => u t y i) x) =
      -D i (fun y => q t y - p t y) x + ν * lap (fun y => v t y i - u t y i) x
    rw [lap_sub ((hv.space t ht).smooth i) ((hu.space t ht).smooth i),
      D_sub ((hv.pressure t ht).smooth.differentiable (by norm_num))
        ((hu.pressure t ht).smooth.differentiable (by norm_num))]
    simp only [Fin.sum_univ_three] at huv hvv ⊢
    linear_combination hvv - huv
  have he : ∀ t ∈ Icc 0 T, ∀ x, e t x = 0 := by
    apply difference_zero (B := BV + BU) hT.le hν (add_nonneg hBV hBU)
      (fun t ht => (hv.space t ht).sub (hu.space t ht))
      (fun t ht i => ((hv.space t ht).smooth i).of_le (by norm_num))
      (fun t ht => (hv.space t ht).per)
      (fun t ht i => ((hu.space t ht).smooth i).of_le (by norm_num))
      (fun t ht => (hv.pressure t ht).sub (hu.pressure t ht))
      (fun t ht x i => (hVb t ht x i).trans (le_add_of_nonneg_right hBU))
      (fun t ht x i => (hDVb t ht x i i).trans (le_add_of_nonneg_right hBU))
      (fun t ht x i k => (hDUb t ht x i k).trans (le_add_of_nonneg_left hBV))
      hvpde.1 hediv hePDE (fun i => (hv.joint i).sub (hu.joint i))
      (fun i => (hv.derivative_joint i).sub (hu.derivative_joint i))
    · intro t ht x i
      exact (hv.pointwise_time t ht x i).sub (hu.pointwise_time t ht x i)
    · intro x
      ext i
      simp [h0 x]
  have hvel (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) : v t x = u t x := by
    ext i
    exact sub_eq_zero.mp (congrFun (he t ht x) i)
  refine ⟨hvel, ?_⟩
  intro t ht
  have hslice : v t = u t := funext (hvel t ht)
  have htime (x : Space) (i : Fin 3) : dv t x i = du t x i := by
    have hh := (hu.pointwise_time t ht x i).congr
      (fun s hs => congrFun (hvel s hs x) i) (congrFun (hvel t ht x) i)
    exact ((hv.pointwise_time t ht x i).derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
      (hh.derivWithin (uniqueDiffOn_Icc hT t ht))
  have hgrad (x : Space) (i : Fin 3) : D i (fun y => q t y - p t y) x = 0 := by
    have h1 := hupde.2 t ht x i
    have h2 := hvpde.2 t ht x i
    rw [htime, hslice] at h2
    rw [D_sub ((hv.pressure t ht).smooth.differentiable (by norm_num))
      ((hu.pressure t ht).smooth.differentiable (by norm_num))]
    linarith only [h1, h2]
  have hpq := (hv.pressure t ht).sub (hu.pressure t ht)
  have hh := pressure_zero_of_gradient_zero (hpq.smooth.differentiable (by norm_num))
    (by rw [integral_sub (integrable_continuous (hv.pressure t ht).smooth.continuous)
        (integrable_continuous (hu.pressure t ht).smooth.continuous),
      hv.pressure_mean t ht, hu.pressure_mean t ht,sub_self]) hgrad
  intro x
  exact sub_eq_zero.mp (hh x)

def dt (u : VectorField 3) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  derivWithin (fun s => u s x i) (Ici 0) t

structure ComparisonClass (u : VectorField 3) (p : ScalarField 3) : Prop where
  velocity_slices : ∀ t ≥ 0, ∀ i, ContDiff ℝ 2 (fun x => u t x i)
  pressure_slices : ∀ t ≥ 0, ContDiff ℝ 1 (p t)
  velocity_periodic : ∀ t ≥ 0, FactorsThrough (u t) PeriodicSpace.cover
  pressure_periodic : ∀ t ≥ 0, periodic (p t)
  pressure_mean : ∀ t ≥ 0, (∫ x, p t x ∂measure) = 0
  time_derivative : ∀ t ≥ 0, ∀ x i,
    HasDerivWithinAt (fun s => u s x i) (dt u t x i) (Ici 0) t
  velocity_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  time_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => dt u y.1 y.2 i) (Icc 0 T ×ˢ univ)
  gradient_continuous : ∀ T > 0, ∀ i k,
    ContinuousOn (fun y : ℝ × Space => D k (fun x => u y.1 x i) y.2) (Icc 0 T ×ˢ univ)
  second_continuous : ∀ T > 0, ∀ i k l,
    ContinuousOn (fun y : ℝ × Space => D l (D k (fun x => u y.1 x i)) y.2) (Icc 0 T ×ˢ univ)
  pressure_continuous : ∀ T > 0,
    ContinuousOn (fun y : ℝ × Space => p y.1 y.2) (Icc 0 T ×ˢ univ)
  pressure_gradient_continuous : ∀ T > 0, ∀ i,
    ContinuousOn (fun y : ℝ × Space => D i (p y.1) y.2) (Icc 0 T ×ˢ univ)

theorem SliceH2.of_smooth_periodic {u : Space → Vect}
    (hs : ∀ i, ContDiff ℝ 2 (fun x => u x i))
    (hp : FactorsThrough u PeriodicSpace.cover) : SliceH2 u :=
  ⟨hs,fun i _ _ h => congrFun (hp h) i,fun i => memLp_continuous (hs i).continuous 2,
    fun i k => memLp_continuous (contDiff_D (hs i) k).continuous 2,
    fun i k l => memLp_continuous (continuous_D (contDiff_D (hs i) k) l) 2⟩

theorem PressureH1.of_smooth_periodic {p : Space → ℝ}
    (hs : ContDiff ℝ 1 p) (hp : periodic p) : PressureH1 p :=
  ⟨hs,hp,memLp_continuous hs.continuous 2,fun i => memLp_continuous (continuous_D hs i) 2⟩

theorem finite_cylinder_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → Space → E} {T : ℝ}
    (hc : ContinuousOn (uncurry f) (Icc 0 T ×ˢ univ))
    (hp : ∀ t ∈ Icc 0 T, FactorsThrough (f t) PeriodicSpace.cover) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x, ‖f t x‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod
    (isCompact_Icc : IsCompact (Icc (0 : Space) 1))).exists_bound_of_continuousOn
    (hc.mono (prod_mono Subset.rfl (subset_univ _)))
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro t ht X
  let Y : Space := fun i => Int.fract (X i)
  have hXY : PeriodicSpace.cover X = PeriodicSpace.cover Y := by
    apply Periodization.cover_eq_iff.mpr
    refine ⟨fun i => ⌊X i⌋,?_⟩
    ext i
    exact (sub_add_cancel _ _).symm
  rw [hp t ht hXY]
  exact (hC (t,Y) ⟨ht,⟨fun i => Int.fract_nonneg _,fun i => (Int.fract_lt_one _).le⟩⟩).trans
    (le_max_right _ _)

theorem ComparisonClass.bounds {u : VectorField 3} {p : ScalarField 3}
    (h : ComparisonClass u p) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧
    (∀ t ∈ Icc 0 T, ∀ x i, |u t x i| ≤ B) ∧
    (∀ t ∈ Icc 0 T, ∀ x i k, |D k (fun y => u t y i) x| ≤ B) := by
  obtain ⟨B₁,hB₁,hb₁⟩ := finite_cylinder_bound
    (continuousOn_pi.mpr (h.velocity_continuous T hT))
    (fun t ht => h.velocity_periodic t ht.1)
  obtain ⟨B₂,hB₂,hb₂⟩ := finite_cylinder_bound
    (f := fun t x i k => D k (fun y => u t y i) x)
    (continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (h.gradient_continuous T hT i)))
    (fun t ht X Y hXY => funext (fun i => funext (fun k =>
      periodic_D ((h.velocity_slices t ht.1 i).differentiable (by norm_num))
        (fun _ _ hxy => congrFun (h.velocity_periodic t ht.1 hxy) i) k hXY)))
  refine ⟨B₁+B₂,add_nonneg hB₁ hB₂,?_,?_⟩
  · intro t ht x i
    exact (norm_le_pi_norm (u t x) i).trans ((hb₁ t ht x).trans (le_add_of_nonneg_right hB₂))
  · intro t ht x i k
    exact ((norm_le_pi_norm (fun k => D k (fun y => u t y i) x) k).trans
      (norm_le_pi_norm (fun i k => D k (fun y => u t y i) x) i)).trans
      ((hb₂ t ht x).trans (le_add_of_nonneg_left hB₁))

theorem ComparisonClass.energyRegularOn {u : VectorField 3} {p : ScalarField 3}
    (h : ComparisonClass u p) {T : ℝ} (hT : 0 < T) : EnergyRegularOn u (dt u) p T :=
  ⟨fun t ht => SliceH2.of_smooth_periodic (h.velocity_slices t ht.1) (h.velocity_periodic t ht.1),
    fun t ht => PressureH1.of_smooth_periodic (h.pressure_slices t ht.1) (h.pressure_periodic t ht.1),
    fun t ht => h.pressure_mean t ht.1,
    fun t ht x i => (h.time_derivative t ht.1 x i).mono Icc_subset_Ici_self,
    h.velocity_continuous T hT,h.time_continuous T hT,h.bounds hT⟩

theorem spatialD_eq {F : ScalarField 3} {t : ℝ}
    (hf : Differentiable ℝ (F t)) (i : Fin 3) (X : Space) :
    spatialD i F t X = D i (F t) X :=
  SpatialCalculus.partialD_eq_fderiv i hf X

theorem second_spatialD_eq {F : ScalarField 3} {t : ℝ}
    (hf : ContDiff ℝ 2 (F t)) (i k : Fin 3) (X : Space) :
    spatialD i (spatialD k F) t X = D i (D k (F t)) X := by
  change deriv (fun s => spatialD k F t (update X i s)) (X i) = _
  simp_rw [spatialD_eq (hf.differentiable (by norm_num))]
  exact spatialD_eq (F := fun _ => D k (F t)) (t := t)
    ((contDiff_D hf k).differentiable (by norm_num)) i X

theorem laplacian_eq {F : ScalarField 3} {t : ℝ}
    (hf : ContDiff ℝ 2 (F t)) (X : Space) : laplacian F t X = lap (F t) X := by
  simp only [laplacian,lap,second_spatialD_eq hf]

theorem ComparisonClass.solvesOn {ν : ℝ} {u f : VectorField 3} {p : ScalarField 3}
    (h : ComparisonClass u p) (hNS : NavierStokes ν u p f) (T : ℝ) :
    solvesOn ν f u (dt u) p T := by
  have hd (t : ℝ) (ht : 0 ≤ t) (i k : Fin 3) (X : Space) :
      spatialD k (fun s y => u s y i) t X = D k (fun y => u t y i) X :=
    spatialD_eq (F := fun s y => u s y i) (t := t)
      ((h.velocity_slices t ht i).differentiable (by norm_num)) k X
  have hl (t : ℝ) (ht : 0 ≤ t) (i : Fin 3) (X : Space) :
      laplacian (fun s y => u s y i) t X = lap (fun y => u t y i) X :=
    laplacian_eq (F := fun s y => u s y i) (h.velocity_slices t ht i) X
  refine ⟨?_,?_⟩
  · intro t ht X
    have hh := hNS.2.1 t ht.1 X
    simpa only [divergence,hd t ht.1] using hh
  · intro t ht X i
    have hh := hNS.1 t ht.1 X i
    simpa only [advection,hd t ht.1,
      spatialD_eq ((h.pressure_slices t ht.1).differentiable (by norm_num)),
      hl t ht.1,timeD,dt] using hh

theorem comparison_unique {ν : ℝ} {f u v : VectorField 3} {p q : ScalarField 3}
    (hν : 0 ≤ ν) (hu : ComparisonClass u p) (hv : ComparisonClass v q)
    (H : NavierStokes ν u p f) (G : NavierStokes ν v q f) :
    ∀ t ≥ 0, (∀ x, v t x = u t x) ∧ (∀ x, q t x = p t x) := by
  intro t ht
  have hT : 0 < t+1 := by linarith only [ht]
  have hh := unique_velocity_and_pressure hT hν (hu.energyRegularOn hT)
    (hv.energyRegularOn hT) (hu.solvesOn H _) (hv.solvesOn G _)
    (fun x => (G.2.2 x).trans (H.2.2 x).symm)
  exact ⟨hh.1 t ⟨ht,by linarith⟩,hh.2 t ⟨ht,by linarith⟩⟩

end VelocityDetection.TorusClass
end

end OAI

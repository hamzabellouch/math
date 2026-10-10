import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Cylinder

namespace OAI

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

theorem periodic_eq_zero_of_ae {f : Space → ℝ} (hf : Continuous f) (hp : periodic f)
    (hz : f =ᵐ[measure] 0) : ∀ x, f x = 0 := by
  have ha : ∀ᵐ X : Coord 2 ∂volume, ∀ z : ℝ, f (X,z) = 0 := by
    have hh := Measure.ae_ae_of_ae_prod hz
    filter_upwards [hh] with X hX
    have hI : EqOn (fun z : ℝ => f (X,z)) 0 (Ioc 0 1) :=
      Measure.eqOn_Ioc_of_ae_eq volume hX (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
        continuousOn_const
    have h0 : f (X,0) = 0 := by
      have h1 := hI (show (1 : ℝ) ∈ Ioc 0 1 by norm_num)
      have hp' : f (X,1) = f (X,0) := by simpa only [zero_add] using hp X 0
      simpa only [Pi.zero_apply, hp'] using h1
    intro z
    have hper : Function.Periodic (fun z => f (X,z)) 1 := hp X
    have hfrac : f (X,Int.fract z) = f (X,z) := by
      simpa only [Int.fract, mul_one] using hper.sub_int_mul_eq (x := z) (Int.floor z)
    rw [← hfrac]
    rcases eq_or_lt_of_le (Int.fract_nonneg z) with h | h
    · rw [← h]; exact h0
    · exact hI ⟨h, (Int.fract_lt_one z).le⟩
  rintro ⟨X,z⟩
  have hae : (fun X : Coord 2 => f (X,z)) =ᵐ[volume] 0 := ha.mono (fun X hX => hX z)
  have heq := Measure.eq_of_ae_eq hae (hf.comp (continuous_id.prodMk continuous_const)) continuous_const
  exact congrFun heq X

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

theorem energy_gronwall_zero {F F' : ℝ → ℝ} {C T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn F (Icc 0 T))
    (hder : ∀ t ∈ Ioo 0 T, HasDerivAt F (F' t) t)
    (hb : ∀ t ∈ Ioo 0 T, F' t ≤ C * F t) (h0 : F 0 = 0)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ F t) : ∀ t ∈ Icc 0 T, F t = 0 := by
  let G : ℝ → ℝ := fun t => Real.exp (-C * t) * F t
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt G (Real.exp (-C*t) * (F' t - C * F t)) t := by
    apply (((hasDerivAt_id t).const_mul (-C)).exp.mul (hder t ht)).congr_deriv
    dsimp only [id]
    ring
  have hG : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t ht).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hb t ht))
  intro t ht
  have hle := hG (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht ht.1
  have hG0 : G 0 = 0 := by simp [G, h0]
  rw [hG0] at hle
  have hf : F t ≤ 0 := by
    change Real.exp (-C*t) * F t ≤ 0 at hle
    nlinarith only [hle, Real.exp_pos (-C*t)]
  exact le_antisymm hf (hn t ht)

theorem difference_zero
    {e de v U : ℝ → Space → Vect} {q : ℝ → Space → ℝ}
    {E dE : ℝ → Fin 3 → L2Space} {ν B T : ℝ}
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
    (hc : ∀ i, ContinuousOn (fun t => E t i) (Icc 0 T))
    (hE : ∀ t ∈ Icc 0 T, ∀ i, (fun x => E t i x) =ᵐ[measure] (fun x => e t x i))
    (hdE : ∀ t ∈ Icc 0 T, ∀ i, (fun x => dE t i x) =ᵐ[measure] (fun x => de t x i))
    (hder : ∀ t ∈ Icc 0 T, ∀ i, HasDerivWithinAt (fun t => E t i) (dE t i) (Icc 0 T) t)
    (h0 : ∀ x, e 0 x = 0) : ∀ t ∈ Icc 0 T, ∀ x, e t x = 0 := by
  have hderF (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun t => energy (e t)) (2 * work (e t) (de t)) t :=
    (energy_hasDerivWithinAt (s := Icc 0 T) (t := t) ⟨ht.1.le, ht.2.le⟩ hE (hdE t ⟨ht.1.le, ht.2.le⟩)
      (hder t ⟨ht.1.le, ht.2.le⟩)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hb (t : ℝ) (ht : t ∈ Ioo 0 T) : 2 * work (e t) (de t) ≤ (6*B) * energy (e t) := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have hde (i : Fin 3) : MemLp (fun x => de t x i) 2 measure :=
      (memLp_congr_ae (hdE t ht' i)).mp (Lp.memLp (dE t i))
    have hh := difference_energy_inequality hν hB (he t ht') hde (hv t ht') (hvp t ht')
      (hU t ht') (hq t ht') (hvb t ht') (hDvb t ht') (hDUb t ht') (hvdiv t ht')
      (hediv t ht') (hpde t ht')
    nlinarith only [hh]
  have hz := energy_gronwall_zero hT (continuousOn_energy hc hE) hderF hb
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

theorem measure_univ : measure univ = ⊤ := by
  rw [measure, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.restrict_apply_univ, Real.volume_Ioc]
  have hvol : (volume : Measure (Coord 2)) univ = ⊤ := by
    rw [volume_pi, Measure.pi_univ, Fin.prod_univ_two, Real.volume_univ]
    simp
  rw [hvol]
  norm_num

theorem fderiv_eq_zero_of_D_eq_zero {q : Space → ℝ} {x : Space}
    (hq : ∀ i, D i q x = 0) : fderiv ℝ q x = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  have hy : y = y.1 0 • frame 0 + y.1 1 • frame 1 + y.2 • frame 2 := by
    ext i
    · fin_cases i <;> simp [frame]
    · simp [frame]
  change fderiv ℝ q x y = 0
  rw [hy]
  dsimp only [D] at hq
  simp only [map_add, map_smul, hq, smul_zero, add_zero]

theorem pressure_zero_of_gradient_zero {q : Space → ℝ}
    (hq : Differentiable ℝ q) (h2 : MemLp q 2 measure)
    (hD : ∀ x i, D i q x = 0) : ∀ x, q x = 0 := by
  have hconst : q = fun _ => q 0 := funext fun x =>
    is_const_of_fderiv_eq_zero hq (fun x => fderiv_eq_zero_of_D_eq_zero (hD x)) x 0
  rw [hconst] at h2
  have h0 : q 0 = 0 := by
    rcases (memLp_const_iff (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp h2 with h | h
    · exact h
    · simp only [measure_univ, lt_self_iff_false] at h
  intro x
  rw [hconst, h0]

structure EnergyRegularOn (u du : ℝ → Space → Vect) (p : ℝ → Space → ℝ)
    (T : ℝ) : Prop where
  space : ∀ t ∈ Icc 0 T, SliceH2 (u t)
  pressure : ∀ t ∈ Icc 0 T, PressureH1 (p t)
  pointwise_time : ∀ t ∈ Icc 0 T, ∀ x i,
    HasDerivWithinAt (fun s => u s x i) (du t x i) (Icc 0 T) t
  strong_time : ∃ E dE : ℝ → Fin 3 → L2Space,
    (∀ i, ContinuousOn (fun t => E t i) (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => E t i x) =ᵐ[measure] (fun x => u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => dE t i x) =ᵐ[measure] (fun x => du t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i,
      HasDerivWithinAt (fun t => E t i) (dE t i) (Icc 0 T) t)
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
  rcases hu.strong_time with ⟨U, dU, hUc, hUr, hdUr, hUd⟩
  rcases hv.strong_time with ⟨V, dV, hVc, hVr, hdVr, hVd⟩
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
    apply difference_zero (E := fun t i => V t i - U t i)
      (dE := fun t i => dV t i - dU t i) (B := BV + BU) hT.le hν (add_nonneg hBV hBU)
      (fun t ht => (hv.space t ht).sub (hu.space t ht))
      (fun t ht i => ((hv.space t ht).smooth i).of_le (by norm_num))
      (fun t ht => (hv.space t ht).per)
      (fun t ht i => ((hu.space t ht).smooth i).of_le (by norm_num))
      (fun t ht => (hv.pressure t ht).sub (hu.pressure t ht))
      (fun t ht x i => (hVb t ht x i).trans (le_add_of_nonneg_right hBU))
      (fun t ht x i => (hDVb t ht x i i).trans (le_add_of_nonneg_right hBU))
      (fun t ht x i k => (hDUb t ht x i k).trans (le_add_of_nonneg_left hBV))
      hvpde.1 hediv hePDE (fun i => (hVc i).sub (hUc i))
    · intro t ht i
      filter_upwards [Lp.coeFn_sub (V t i) (U t i), hVr t ht i, hUr t ht i] with x hx hvx hux
      simpa only [Pi.sub_apply, e, hvx, hux] using hx
    · intro t ht i
      filter_upwards [Lp.coeFn_sub (dV t i) (dU t i), hdVr t ht i, hdUr t ht i] with x hx hvx hux
      simpa only [Pi.sub_apply, de, hvx, hux] using hx
    · intro t ht i
      exact (hVd t ht i).sub (hUd t ht i)
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
    hpq.square_integrable hgrad
  intro x
  exact sub_eq_zero.mp (hh x)

def dt (u : ℝ → Space → Vect) (t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  derivWithin (fun s => u s x i) (Ici 0) t

theorem spaceOuterMeasureClass : OuterMeasureClass (Measure Space) Space :=
  Measure.instOuterMeasureClass

def continuousL2On (g : ℝ → Space → ℝ) (T : ℝ) : Prop :=
  letI : IsTopologicalAddGroup ℝ := instIsTopologicalAddGroupReal
  letI := spaceOuterMeasureClass
  ∃ G : ℝ → L2Space, ContinuousOn G (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (fun x => G t x) =ᵐ[measure] g t

def continuousH2On (u : ℝ → Space → Vect) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, SliceH2 (u t)) ∧
  (∀ i, continuousL2On (fun t x => u t x i) T) ∧
  (∀ i k, continuousL2On (fun t => D k (fun x => u t x i)) T) ∧
  (∀ i k l, continuousL2On (fun t => D l (D k (fun x => u t x i))) T)

def continuousH1On (p : ℝ → Space → ℝ) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, PressureH1 (p t)) ∧ continuousL2On p T ∧
  (∀ i, continuousL2On (fun t => D i (p t)) T)

def C1L2On (u : ℝ → Space → Vect) (T : ℝ) : Prop :=
  letI : IsTopologicalAddGroup ℝ := instIsTopologicalAddGroupReal
  letI := spaceOuterMeasureClass
  ∃ U dU : ℝ → Fin 3 → L2Space,
    (∀ i, ContinuousOn (fun t => U t i) (Icc 0 T)) ∧
    (∀ i, ContinuousOn (fun t => dU t i) (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => U t i x) =ᵐ[measure] (fun x => u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i, (fun x => dU t i x) =ᵐ[measure] (fun x => dt u t x i)) ∧
    (∀ t ∈ Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => U s i) (dU t i) (Icc 0 T) t)

structure ComparisonClass (u : ℝ → Space → Vect) (p : ℝ → Space → ℝ) : Prop where
  velocity_H2 : ∀ T > 0, continuousH2On u T
  velocity_C1L2 : ∀ T > 0, C1L2On u T
  pressure_H1 : ∀ T > 0, continuousH1On p T
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
  bounds : ∀ T > 0, ∃ B : ℝ, 0 ≤ B ∧
    (∀ t ∈ Icc 0 T, ∀ x i, |u t x i| ≤ B) ∧
    (∀ t ∈ Icc 0 T, ∀ x i k, |D k (fun y => u t y i) x| ≤ B)

theorem ComparisonClass.energyRegularOn
    {u : ℝ → Space → Vect} {p : ℝ → Space → ℝ}
    (h : ComparisonClass u p) {T : ℝ} (hT : 0 < T) : EnergyRegularOn u (dt u) p T := by
  rcases h.velocity_C1L2 T hT with ⟨U, dU, hc, _, hr, hdr, hd⟩
  exact ⟨(h.velocity_H2 T hT).1, (h.pressure_H1 T hT).1,
    fun t ht x i => (h.time_derivative t ht.1 x i).mono Icc_subset_Ici_self,
    ⟨U, dU, hc, hr, hdr, hd⟩, h.bounds T hT⟩

def navierStokes (ν : ℝ) (f u : ℝ → Space → Vect) (p : ℝ → Space → ℝ) : Prop :=
  (∀ t ≥ 0, ∀ x, div (u t) x = 0) ∧
  (∀ t ≥ 0, ∀ x i,
    dt u t x i + (∑ k, u t x k * D k (fun y => u t y i) x) =
     -D i (p t) x + ν * lap (fun y => u t y i) x + f t x i) ∧
  (∀ x, u 0 x = 0)

theorem comparison_unique
    {ν : ℝ} {f u v : ℝ → Space → Vect} {p q : ℝ → Space → ℝ}
    (hν : 0 ≤ ν) (hu : ComparisonClass u p) (hv : ComparisonClass v q)
    (H : navierStokes ν f u p) (G : navierStokes ν f v q) :
    ∀ t ≥ 0, (∀ x, v t x = u t x) ∧ (∀ x, q t x = p t x) := by
  intro t ht
  have hT : 0 < t + 1 := by linarith only [ht]
  have huP : solvesOn ν f u (dt u) p (t + 1) :=
    ⟨fun s hs => H.1 s hs.1, fun s hs => H.2.1 s hs.1⟩
  have hvP : solvesOn ν f v (dt v) q (t + 1) :=
    ⟨fun s hs => G.1 s hs.1, fun s hs => G.2.1 s hs.1⟩
  have hh := unique_velocity_and_pressure hT hν (hu.energyRegularOn hT)
    (hv.energyRegularOn hT) huP hvP (fun x => (G.2.2 x).trans (H.2.2 x).symm)
  have hmem : t ∈ Icc 0 (t + 1) := ⟨ht, by linarith⟩
  exact ⟨hh.1 t hmem, hh.2 t hmem⟩

def join (x : Space) : Coord 3 :=
  letI := neZeroTwo
  ![x.1 0, x.1 1, x.2]

def split (y : Coord 3) : Space := (horizontal y, y 2)

end VelocityDetection.Cylinder
end

end OAI

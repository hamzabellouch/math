import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivativesFderiv

namespace OAI

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

abbrev Space := Coord 2 × ℝ

abbrev Vect := Fin 3 → ℝ

def measure : Measure Space := volume.prod (volume.restrict (Ioc (0 : ℝ) 1))

def periodic (f : Space → ℝ) : Prop := ∀ X z, f (X, z + 1) = f (X, z)

def frame (i : Fin 3) : Space := ![(![1, 0], 0), (![0, 1], 0), (0, 1)] i

def D (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ := fderiv ℝ f x (frame i)

abbrev div (v : Space → Vect) (x : Space) : ℝ := ∑ i, D i (fun y => v y i) x

abbrev lap (f : Space → ℝ) (x : Space) : ℝ := ∑ i, D i (D i f) x

theorem D_mul {f g : Space → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (x : Space) :
    D i (fun y => f y * g y) x = D i f x * g x + f x * D i g x := by
  simp only [D, fderiv_fun_mul (hf x) (hg x), add_apply,
    smul_apply, smul_eq_mul]
  ring

theorem D_sub {f g : Space → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (x : Space) :
    D i (fun y => f y - g y) x = D i f x - D i g x := by
  simp only [D, fderiv_fun_sub (hf x) (hg x), sub_apply]

theorem continuous_D {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (D i f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem contDiff_D {f : Space → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    ContDiff ℝ 1 (D i f) := (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem differential_horizontal {f : Space → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 2) (X : Coord 2) (z : ℝ) :
    fderiv ℝ (fun Y : Coord 2 => f (Y, z)) X (Pi.single i 1) = D i.castSucc f (X, z) := by
  have hp : HasFDerivAt (fun Y : Coord 2 => (Y, z))
      ((ContinuousLinearMap.id ℝ (Coord 2)).prod 0) X :=
    (hasFDerivAt_id X).prodMk (hasFDerivAt_const z X)
  have hh := ((hf (X, z)).hasFDerivAt.comp X hp).fderiv
  change fderiv ℝ (fun Y : Coord 2 => f (Y, z)) X = _ at hh
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, D]
  congr 1
  fin_cases i <;> simp [frame]
  all_goals ext j; fin_cases j <;> simp

theorem hasDerivAt_vertical {f : Space → ℝ} (hf : Differentiable ℝ f)
    (X : Coord 2) (z : ℝ) :
    HasDerivAt (fun r : ℝ => f (X, r)) (D 2 f (X, z)) z := by
  have hp : HasDerivAt (fun r : ℝ => (X, r)) (0, 1) z :=
    (hasDerivAt_const z X).prodMk (hasDerivAt_id z)
  exact ((hf (X, z)).hasFDerivAt.comp_hasDerivAt z hp)

theorem integral_mul_D {f g : Space → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : periodic f) (hgp : periodic g) (i : Fin 3)
    (hfg : Integrable (fun x => f x * g x) measure)
    (hdfg : Integrable (fun x => D i f x * g x) measure)
    (hfdg : Integrable (fun x => f x * D i g x) measure) :
    (∫ x, f x * D i g x ∂measure) = -(∫ x, D i f x * g x ∂measure) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have horiz (j : Fin 2) (hij : i = j.castSucc) :
      (∫ x, f x * D i g x ∂measure) = -(∫ x, D i f x * g x ∂measure) := by
    subst i
    unfold measure at hfg hdfg hfdg ⊢
    rw [integral_prod_symm _ hfdg, integral_prod_symm _ hdfg, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hfg.prod_left_ae, hdfg.prod_left_ae, hfdg.prod_left_ae] with z h0 h1 h2
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (v := Pi.single j 1) (f := fun X : Coord 2 => f (X, z))
      (g := fun X : Coord 2 => g (X, z))
      (by simpa only [differential_horizontal hfd] using h1)
      (by simpa only [differential_horizontal hgd] using h2) h0
      (fun X _ => (hfd.comp (differentiable_id.prodMk (differentiable_const z))) X)
      (fun X _ => (hgd.comp (differentiable_id.prodMk (differentiable_const z))) X)
    simpa only [differential_horizontal hfd, differential_horizontal hgd] using hh
  fin_cases i
  · exact horiz 0 rfl
  · exact horiz 1 rfl
  · unfold measure at hfdg hdfg ⊢
    rw [integral_prod _ hfdg, integral_prod _ hdfg, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with X
    have hi1 : IntervalIntegrable (fun z : ℝ => D 2 f (X, z)) volume 0 1 :=
      ((continuous_D hf 2).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun z : ℝ => D 2 g (X, z)) volume 0 1 :=
      ((continuous_D hg 2).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hb1 : f (X, 1) = f (X, 0) := by simpa only [zero_add] using hfp X 0
    have hb2 : g (X, 1) = g (X, 0) := by simpa only [zero_add] using hgp X 0
    have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun z _ => hasDerivAt_vertical hfd X z) (fun z _ => hasDerivAt_vertical hgd X z) hi1 hi2
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), hb1, hb2, sub_self, zero_sub] at hh
    exact hh

theorem periodic_D {f : Space → ℝ} (hf : Differentiable ℝ f)
    (hfp : periodic f) (i : Fin 3) : periodic (D i f) := by
  intro X z
  let a : Space := (0, 1)
  have heq : (fun y : Space => f (y + a)) = f := by
    funext ⟨Y, z⟩
    simpa [a] using hfp Y z
  have hh := (hf ((X, z) + a)).hasFDerivAt.comp (X, z)
    ((hasFDerivAt_id (X, z)).add_const a)
  change HasFDerivAt (fun y : Space => f (y + a))
    (fderiv ℝ f ((X, z) + a) ∘L ContinuousLinearMap.id ℝ Space) (X, z) at hh
  rw [heq] at hh
  have hd := hh.fderiv
  simpa [D, a, ContinuousLinearMap.comp_id] using
    (congrArg (fun l : Space →L[ℝ] ℝ => l (frame i)) hd).symm

theorem periodic_sub {f g : Space → ℝ} (hf : periodic f) (hg : periodic g) :
    periodic (fun x => f x - g x) := fun X z => by dsimp only; rw [hf, hg]

theorem periodic_mul {f g : Space → ℝ} (hf : periodic f) (hg : periodic g) :
    periodic (fun x => f x * g x) := fun X z => by dsimp only; rw [hf, hg]

theorem integrable_mul_L2 {f g : Space → ℝ}
    (hf : MemLp f 2 measure) (hg : MemLp g 2 measure) :
    Integrable (fun x => f x * g x) measure := hf.integrable_mul hg

theorem integrable_sq_L2 {f : Space → ℝ} (hf : MemLp f 2 measure) :
    Integrable (fun x => (f x)^2) measure := by
  simpa only [sq] using integrable_mul_L2 hf hf

theorem integrable_bdd_mul {a f : Space → ℝ} {B : ℝ}
    (ha : Continuous a) (hb : ∀ x, |a x| ≤ B) (hf : Integrable f measure) :
    Integrable (fun x => a x * f x) measure :=
  hf.bdd_mul ha.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hb x)

theorem integral_transport_energy {e : Space → ℝ} {v : Space → Vect} {B : ℝ}
    (he : ContDiff ℝ 1 e) (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i))
    (hep : periodic e) (hvp : ∀ i, periodic (fun x => v x i))
    (he2 : MemLp e 2 measure) (hDe2 : ∀ i, MemLp (D i e) 2 measure)
    (hvb : ∀ x i, |v x i| ≤ B) (hDvb : ∀ x i, |D i (fun y => v y i) x| ≤ B)
    (hvdiv : ∀ x, div v x = 0) :
    (∫ x, ∑ i, v x i * e x * D i e x ∂measure) = 0 := by
  have hdi (i : Fin 3) : Integrable (fun x => D i (fun y => v y i) x * (e x)^2) measure :=
    integrable_bdd_mul (continuous_D (hv i) i) (fun x => hDvb x i) (integrable_sq_L2 he2)
  have hti (i : Fin 3) : Integrable (fun x => v x i * e x * D i e x) measure := by
    simpa only [mul_assoc] using integrable_bdd_mul (hv i).continuous (fun x => hvb x i)
      (integrable_mul_L2 he2 (hDe2 i))
  have hid (i : Fin 3) :
      2 * (∫ x, v x i * e x * D i e x ∂measure) =
        -(∫ x, D i (fun y => v y i) x * (e x)^2 ∂measure) := by
    have hdsq (x : Space) : D i (fun y => (e y)^2) x = 2 * e x * D i e x := by
      simp only [sq, D_mul (he.differentiable (by norm_num)) (he.differentiable (by norm_num))]
      ring
    have hsqper : periodic (fun x => (e x)^2) := fun X z => by dsimp only; rw [hep]
    have hh := integral_mul_D (hv i) (he.pow 2) (hvp i) hsqper i
      (integrable_bdd_mul (hv i).continuous (fun x => hvb x i) (integrable_sq_L2 he2)) (hdi i)
      (by
        simp_rw [hdsq]
        convert (hti i).const_mul 2 using 1
        ext x
        ring)
    simpa only [hdsq, show (fun x => v x i * (2 * e x * D i e x)) =
      (fun x => 2 * (v x i * e x * D i e x)) by funext x; ring,
      integral_const_mul] using hh
  have hi : Integrable (fun x => ∑ i, v x i * e x * D i e x) measure :=
    integrable_finsetSum _ (fun i _ => hti i)
  have hh : 2 * (∫ x, ∑ i, v x i * e x * D i e x ∂measure) = 0 := by
    rw [integral_finsetSum _ (fun i _ => hti i), Finset.mul_sum]
    simp_rw [hid]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hdi i)]
    have hzero : (fun x => ∑ i, D i (fun y => v y i) x * (e x)^2) = (fun _ => 0) := by
      funext x
      rw [← Finset.sum_mul]
      change div v x * (e x)^2 = 0
      rw [hvdiv, zero_mul]
    rw [hzero, integral_zero, neg_zero]
  linarith

theorem integral_pressure_work {e : Space → Vect} {q : Space → ℝ}
    (he : ∀ i, ContDiff ℝ 1 (fun x => e x i)) (hq : ContDiff ℝ 1 q)
    (hep : ∀ i, periodic (fun x => e x i)) (hqp : periodic q)
    (he2 : ∀ i, MemLp (fun x => e x i) 2 measure)
    (hDe2 : ∀ i, MemLp (D i (fun x => e x i)) 2 measure)
    (hq2 : MemLp q 2 measure) (hDq2 : ∀ i, MemLp (D i q) 2 measure)
    (hediv : ∀ x, div e x = 0) :
    (∫ x, ∑ i, e x i * D i q x ∂measure) = 0 := by
  have h1 (i : Fin 3) := integrable_mul_L2 (he2 i) (hDq2 i)
  have h2 (i : Fin 3) := integrable_mul_L2 (hDe2 i) hq2
  rw [integral_finsetSum _ (fun i _ => h1 i)]
  simp_rw [integral_mul_D (he _) hq (hep _) hqp _
    (integrable_mul_L2 (he2 _) hq2) (h2 _) (h1 _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => h2 i)]
  have hz : (fun x => ∑ i, D i (fun y => e y i) x * q x) = (fun _ => 0) := by
    funext x
    rw [← Finset.sum_mul]
    change div e x * q x = 0
    rw [hediv, zero_mul]
  rw [hz, integral_zero, neg_zero]

theorem integral_laplacian_energy {e : Space → ℝ}
    (he : ContDiff ℝ 2 e) (hep : periodic e) (he2 : MemLp e 2 measure)
    (hDe2 : ∀ i, MemLp (D i e) 2 measure)
    (hDDe2 : ∀ i, MemLp (D i (D i e)) 2 measure) :
    (∫ x, e x * lap e x ∂measure) = -(∫ x, ∑ i, (D i e x)^2 ∂measure) := by
  have hi (i : Fin 3) := integrable_mul_L2 he2 (hDDe2 i)
  have hi' (i : Fin 3) := integrable_sq_L2 (hDe2 i)
  simp only [lap, Finset.mul_sum, integral_finsetSum _ (fun i _ => hi i)]
  have he1 : ContDiff ℝ 1 e := he.of_le (by norm_num)
  have hid (i : Fin 3) :
      (∫ x, e x * D i (D i e) x ∂measure) = -(∫ x, (D i e x)^2 ∂measure) := by
    simpa only [sq] using integral_mul_D he1 (contDiff_D he i) hep
      (periodic_D (he1.differentiable (by norm_num)) hep i) i
      (integrable_mul_L2 he2 (hDe2 i)) (integrable_mul_L2 (hDe2 i) (hDe2 i)) (hi i)
  simp_rw [hid]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hi' i)]

theorem stretching_bound (e : Vect) (A : Fin 3 → Fin 3 → ℝ) {B : ℝ}
    (_hB : 0 ≤ B) (hA : ∀ i k, |A i k| ≤ B) :
    -(∑ i, ∑ k, e i * e k * A i k) ≤ 3 * B * (∑ i, (e i)^2) := by
  have hb (i k : Fin 3) : -(e i * e k * A i k) ≤ (B / 2) * ((e i)^2 + (e k)^2) := by
    have hy : |e i * e k| ≤ ((e i)^2 + (e k)^2) / 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith only [sq_nonneg (e i - e k), sq_nonneg (e i + e k)]
    calc
      -(e i * e k * A i k) ≤ |e i * e k * A i k| := neg_le_abs _
      _ = |e i * e k| * |A i k| := abs_mul _ _
      _ ≤ (((e i)^2 + (e k)^2) / 2) * B :=
        mul_le_mul hy (hA i k) (abs_nonneg _) (by positivity)
      _ = (B / 2) * ((e i)^2 + (e k)^2) := by ring
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  calc
    ∑ i, ∑ k, -(e i * e k * A i k) ≤
        ∑ i, ∑ k, (B / 2) * ((e i)^2 + (e k)^2) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hb i k
    _ = 3 * B * (∑ i, (e i)^2) := by
      simp only [Fin.sum_univ_three]
      ring

abbrev energy (e : Space → Vect) : ℝ := ∫ x, ∑ i, (e x i)^2 ∂measure

abbrev work (e g : Space → Vect) : ℝ := ∫ x, ∑ i, e x i * g x i ∂measure

structure SliceH2 (v : Space → Vect) : Prop where
  smooth : ∀ i, ContDiff ℝ 2 (fun x => v x i)
  per : ∀ i, periodic (fun x => v x i)
  square_integrable : ∀ i, MemLp (fun x => v x i) 2 measure
  derivative_square_integrable : ∀ i k, MemLp (D k (fun x => v x i)) 2 measure
  second_square_integrable : ∀ i k l, MemLp (D l (D k (fun x => v x i))) 2 measure

structure PressureH1 (q : Space → ℝ) : Prop where
  smooth : ContDiff ℝ 1 q
  per : periodic q
  square_integrable : MemLp q 2 measure
  derivative_square_integrable : ∀ k, MemLp (D k q) 2 measure

theorem integrable_energy {e : Space → Vect} (h2 : ∀ i, MemLp (fun x => e x i) 2 measure) :
    Integrable (fun x => ∑ i, (e x i)^2) measure :=
  integrable_finsetSum _ (fun i _ => integrable_sq_L2 (h2 i))

theorem integrable_work {e g : Space → Vect}
    (he : ∀ i, MemLp (fun x => e x i) 2 measure)
    (hg : ∀ i, MemLp (fun x => g x i) 2 measure) :
    Integrable (fun x => ∑ i, e x i * g x i) measure :=
  integrable_finsetSum _ (fun i _ => integrable_mul_L2 (he i) (hg i))

theorem energy_nonneg (e : Space → Vect) : 0 ≤ energy e :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem difference_energy_inequality
    {e de v U : Space → Vect} {q : Space → ℝ} {ν B : ℝ}
    (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (he : SliceH2 e) (_hde : ∀ i, MemLp (fun x => de x i) 2 measure)
    (hv : ∀ i, ContDiff ℝ 1 (fun x => v x i))
    (hvp : ∀ i, periodic (fun x => v x i))
    (hU : ∀ i, ContDiff ℝ 1 (fun x => U x i))
    (hq : PressureH1 q)
    (hvb : ∀ x i, |v x i| ≤ B) (hDvb : ∀ x i, |D i (fun y => v y i) x| ≤ B)
    (hDUb : ∀ x i k, |D k (fun y => U y i) x| ≤ B)
    (hvdiv : ∀ x, div v x = 0) (hediv : ∀ x, div e x = 0)
    (hpde : ∀ x i,
      de x i + (∑ k, v x k * D k (fun y => e y i) x) +
        (∑ k, e x k * D k (fun y => U y i) x) =
        -D i q x + ν * lap (fun y => e y i) x) :
    work e de ≤ 3 * B * energy e := by
  have he1 (i : Fin 3) : ContDiff ℝ 1 (fun x => e x i) := (he.smooth i).of_le (by norm_num)
  let tr : Space → ℝ := fun x => ∑ i, ∑ k, v x k * e x i * D k (fun y => e y i) x
  let st : Space → ℝ := fun x => ∑ i, ∑ k, e x i * e x k * D k (fun y => U y i) x
  let pr : Space → ℝ := fun x => ∑ i, e x i * D i q x
  let la : Space → ℝ := fun x => ∑ i, e x i * lap (fun y => e y i) x
  have ht (i k : Fin 3) :
      Integrable (fun x => v x k * e x i * D k (fun y => e y i) x) measure := by
    simpa only [mul_assoc] using integrable_bdd_mul (hv k).continuous (fun x => hvb x k)
      (integrable_mul_L2 (he.square_integrable i) (he.derivative_square_integrable i k))
  have hs (i k : Fin 3) :
      Integrable (fun x => e x i * e x k * D k (fun y => U y i) x) measure := by
    simpa only [mul_comm] using integrable_bdd_mul (continuous_D (hU i) k)
      (fun x => hDUb x i k) (integrable_mul_L2 (he.square_integrable i) (he.square_integrable k))
  have hp (i : Fin 3) := integrable_mul_L2 (he.square_integrable i) (hq.derivative_square_integrable i)
  have hl (i : Fin 3) : Integrable (fun x => e x i * lap (fun y => e y i) x) measure := by
    simp only [lap, Finset.mul_sum]
    exact integrable_finsetSum _ (fun k _ =>
      integrable_mul_L2 (he.square_integrable i) (he.second_square_integrable i k k))
  have hti : Integrable tr measure :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => ht i k))
  have hsi : Integrable st measure :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hs i k))
  have hpi : Integrable pr measure := integrable_finsetSum _ (fun i _ => hp i)
  have hli : Integrable la measure := integrable_finsetSum _ (fun i _ => hl i)
  have htr : (∫ x, tr x ∂measure) = 0 := by
    dsimp [tr]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => ht i k))]
    have hid (i : Fin 3) := integral_transport_energy (he1 i) hv (he.per i) hvp
      (he.square_integrable i) (he.derivative_square_integrable i) hvb hDvb hvdiv
    simp_rw [hid, Finset.sum_const_zero]
  have hpr : (∫ x, pr x ∂measure) = 0 :=
    integral_pressure_work he1 hq.smooth he.per hq.per he.square_integrable
      (fun i => he.derivative_square_integrable i i) hq.square_integrable
      hq.derivative_square_integrable hediv
  have hla : (∫ x, la x ∂measure) ≤ 0 := by
    dsimp [la]
    rw [integral_finsetSum _ (fun i _ => hl i)]
    apply Finset.sum_nonpos
    intro i _
    rw [integral_laplacian_energy (he.smooth i) (he.per i) (he.square_integrable i)
      (he.derivative_square_integrable i) (fun k => he.second_square_integrable i k k)]
    exact neg_nonpos.mpr (integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hb : -(∫ x, st x ∂measure) ≤ 3 * B * energy e := by
    rw [← integral_neg, energy, ← integral_const_mul]
    exact integral_mono hsi.neg ((integrable_energy he.square_integrable).const_mul _)
      (fun x => stretching_bound (e x) (fun i k => D k (fun y => U y i) x) hB (hDUb x))
  have hpoint (x : Space) :
      (∑ i, e x i * de x i) = -tr x - st x - pr x + ν * la x := by
    have hcomp (i : Fin 3) :
        e x i * de x i =
          -(∑ k, v x k * e x i * D k (fun y => e y i) x) -
          (∑ k, e x i * e x k * D k (fun y => U y i) x) -
          e x i * D i q x + ν * (e x i * lap (fun y => e y i) x) := by
      have hi := congrArg (fun r : ℝ => e x i * r) (hpde x i)
      simp only [mul_add, Finset.mul_sum, mul_neg] at hi
      have hswap : (∑ k, e x i * (v x k * D k (fun y => e y i) x)) =
          (∑ k, v x k * e x i * D k (fun y => e y i) x) := by
        apply Finset.sum_congr rfl; intro k _; ring
      simp_rw [hswap, ← mul_assoc] at hi
      simp only [lap, Fin.sum_univ_three] at hi ⊢
      nlinarith only [hi]
    simp only [hcomp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.mul_sum, tr, st, pr, la]
  have hw : work e de = -(∫ x, st x ∂measure) + ν * (∫ x, la x ∂measure) := by
    change (∫ x, (∑ i, e x i * de x i) ∂measure) = _
    simp_rw [hpoint]
    rw [integral_add (f := fun x => -tr x - st x - pr x) (g := fun x => ν * la x)
        ((hti.neg.sub hsi).sub hpi) (hli.const_mul _),
      integral_sub (f := fun x => -tr x - st x) (g := pr) (hti.neg.sub hsi) hpi,
      integral_sub (f := fun x => -tr x) (g := st) hti.neg hsi, integral_neg,
      integral_const_mul, htr, hpr]
    ring
  rw [hw]
  exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hν hla)).trans hb

theorem twoAtLeastTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev LpSpace {α : Type*} [MeasurableSpace α] (E : Type*) [NormedAddCommGroup E]
    (p : ENNReal) (μ : Measure α) : Type _ := Lp E p μ

abbrev L2Space : Type :=
  letI := twoAtLeastTwo
  LpSpace ℝ 2 measure

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

theorem work_eq_L2 (e g : Space → Vect) (E G : Fin 3 → L2Space)
    (hE : ∀ i, (fun x => E i x) =ᵐ[measure] (fun x => e x i))
    (hG : ∀ i, (fun x => G i x) =ᵐ[measure] (fun x => g x i)) :
    work e g = ∑ i, inner ℝ (E i) (G i) := by
  have he (i : Fin 3) : MemLp (fun x => e x i) 2 measure := (memLp_congr_ae (hE i)).mp (Lp.memLp (E i))
  have hg (i : Fin 3) : MemLp (fun x => g x i) 2 measure := (memLp_congr_ae (hG i)).mp (Lp.memLp (G i))
  rw [work, integral_finsetSum _ (fun i _ => integrable_mul_L2 (he i) (hg i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hE i, hG i] with x hx hy
  simp [hx, hy, mul_comm]

theorem energy_hasDerivWithinAt {e de : ℝ → Space → Vect}
    {E dE : ℝ → Fin 3 → L2Space} {s : Set ℝ} {t : ℝ} (ht : t ∈ s)
    (hE : ∀ t ∈ s, ∀ i, (fun x => E t i x) =ᵐ[measure] (fun x => e t x i))
    (hdE : ∀ i, (fun x => dE t i x) =ᵐ[measure] (fun x => de t x i))
    (hder : ∀ i, HasDerivWithinAt (fun t => E t i) (dE t i) s t) :
    HasDerivWithinAt (fun t => energy (e t)) (2 * work (e t) (de t)) s t := by
  have hh := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ => (hder i).norm_sq)
  simp only [← Finset.mul_sum] at hh
  rw [← work_eq_L2 (e t) (de t) (E t) (dE t) (hE t ht) hdE] at hh
  exact hh.congr (fun r hr => energy_eq_L2 (e r) (E r) (hE r hr))
    (energy_eq_L2 (e t) (E t) (hE t ht))

theorem continuousOn_energy {e : ℝ → Space → Vect} {E : ℝ → Fin 3 → L2Space}
    {s : Set ℝ} (hc : ∀ i, ContinuousOn (fun t => E t i) s)
    (hE : ∀ t ∈ s, ∀ i, (fun x => E t i x) =ᵐ[measure] (fun x => e t x i)) :
    ContinuousOn (fun t => energy (e t)) s := by
  have hh := continuousOn_finsetSum Finset.univ (fun i _ => (hc i).norm.pow 2)
  exact hh.congr (fun t ht => energy_eq_L2 (e t) (E t) (hE t ht))

end VelocityDetection.Cylinder
end

end OAI

import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Periodization

namespace OAI

noncomputable section
namespace VelocityDetection.TorusClass
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators

abbrev Space := Coord 3

abbrev Vect := Coord 3

def measure : Measure Space := volume.restrict (Icc (0 : Space) 1)

@[simp] theorem measure_univ : measure univ = 1 := by
  simp [measure, Real.volume_Icc_pi]

instance : IsProbabilityMeasure measure := ⟨measure_univ⟩

def periodic (f : Space → ℝ) : Prop := FactorsThrough f PeriodicSpace.cover

def frame (i : Fin 3) : Space := Pi.single i 1

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

theorem integrable_continuous {f : Space → ℝ} (hf : Continuous f) :
    Integrable f measure := hf.continuousOn.integrableOn_Icc

theorem memLp_continuous {f : Space → ℝ} (hf : Continuous f) (p : ENNReal) :
    MemLp f p measure := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : Space) 1)).exists_bound_of_continuousOn
    hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C ((ae_restrict_mem measurableSet_Icc).mono hC)

theorem periodic_faces {f : Space → ℝ} (hp : periodic f) (i : Fin 3) (x : Coord 2) :
    f (i.insertNth 1 x) = f (i.insertNth 0 x) := by
  apply hp
  apply Periodization.cover_eq_iff.mpr
  refine ⟨Pi.single i 1,?_⟩
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k,rfl⟩
  · simp [Periodization.lattice]
  · simp [Periodization.lattice, Fin.succAbove_ne]

theorem integral_D_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : periodic f) (i : Fin 3) : (∫ x, D i f x ∂measure) = 0 := by
  let F : Fin 3 → Space → ℝ := fun j x => if j = i then f x else 0
  have hF (j : Fin 3) : ContDiff ℝ 1 (F j) := by
    by_cases hj : j = i
    · simpa [F,hj] using hf
    · simp [F,hj,contDiff_const]
  have hD (x : Space) : (∑ j : Fin 3, fderiv ℝ (F j) x (Pi.single j 1)) = D i f x := by
    have he (j : Fin 3) : fderiv ℝ (F j) x (Pi.single j 1) = if j = i then D i f x else 0 := by
      by_cases hj : j = i
      · subst j; simp [F,D,frame]
      · simp [F,hj]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hh := integral_divergence_of_hasFDerivAt_off_countable' (0 : Space) 1
    (by intro j; norm_num) F (fun j => fderiv ℝ (F j)) ∅ countable_empty
    (fun j => (hF j).continuous.continuousOn)
    (fun x _ j => ((hF j).differentiable (by norm_num) x).hasFDerivAt)
    (by simpa only [hD,measure,IntegrableOn] using integrable_continuous (continuous_D hf i))
  simp only [hD] at hh
  change (∫ x in Icc (0 : Space) 1, D i f x) = 0
  rw [hh]
  apply Finset.sum_eq_zero
  intro j _
  have he : (fun x : Coord 2 => F j (j.insertNth 1 x)) =
      (fun x : Coord 2 => F j (j.insertNth 0 x)) := by
    funext x
    by_cases hj : j = i
    · simp only [F,hj,ite_true]
      exact periodic_faces hp i x
    · simp [F,hj]
  change (∫ x in Icc ((0 : Space) ∘ j.succAbove) ((1 : Space) ∘ j.succAbove),
    F j (j.insertNth 1 x)) - (∫ x in Icc ((0 : Space) ∘ j.succAbove) ((1 : Space) ∘ j.succAbove),
    F j (j.insertNth 0 x)) = 0
  rw [he,sub_self]

theorem periodic_D {f : Space → ℝ} (_hf : Differentiable ℝ f)
    (hp : periodic f) (i : Fin 3) : periodic (D i f) := by
  intro X Y hXY
  have hz : PeriodicSpace.cover (Y-X) = 0 := by rw [PeriodicSpace.cover_sub,hXY,sub_self]
  have he : (fun q : Space => f (q+(Y-X))) = f := by
    funext q
    apply hp
    rw [PeriodicSpace.cover_add,hz,add_zero]
  have hh := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := X) (Y-X)
  rw [he,show X+(Y-X) = Y from by abel] at hh
  exact congrArg (fun L : Space →L[ℝ] ℝ => L (frame i)) hh

theorem periodic_sub {f g : Space → ℝ} (hf : periodic f) (hg : periodic g) :
    periodic (fun x => f x - g x) := fun _ _ h => by dsimp only; rw [hf h,hg h]

theorem periodic_mul {f g : Space → ℝ} (hf : periodic f) (hg : periodic g) :
    periodic (fun x => f x * g x) := fun _ _ h => by dsimp only; rw [hf h,hg h]

theorem integral_mul_D {f g : Space → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : periodic f) (hgp : periodic g) (i : Fin 3)
    (_hfg : Integrable (fun x => f x * g x) measure)
    (hdfg : Integrable (fun x => D i f x * g x) measure)
    (hfdg : Integrable (fun x => f x * D i g x) measure) :
    (∫ x, f x * D i g x ∂measure) = -(∫ x, D i f x * g x ∂measure) := by
  have hh := integral_D_eq_zero (hf.mul hg) (periodic_mul hfp hgp) i
  simp only [D_mul (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)),
    integral_add hdfg hfdg] at hh
  linarith only [hh]

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
    have hsqper : periodic (fun x => (e x)^2) := fun X Y h => by dsimp only; rw [hep h]
    have hh := integral_mul_D (hv i) (he.pow 2) (hvp i) hsqper i
      (integrable_bdd_mul (hv i).continuous (fun x => hvb x i) (integrable_sq_L2 he2)) (hdi i)
      (by
        simp_rw [hdsq]
        convert (hti i).const_mul 2 using 1; ext x; ring)
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
  integral_nonneg fun _x => Finset.sum_nonneg fun _i _ => sq_nonneg _

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

theorem continuous_slice {f : ℝ → Space → ℝ} {T t : ℝ}
    (hc : ContinuousOn (uncurry f) (Icc 0 T ×ˢ univ)) (ht : t ∈ Icc 0 T) :
    Continuous (f t) := by
  apply continuousOn_univ.mp
  exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨ht,mem_univ x⟩)

theorem continuous_time {f : ℝ → Space → ℝ} {T : ℝ}
    (hc : ContinuousOn (uncurry f) (Icc 0 T ×ˢ univ)) (x : Space) :
    ContinuousOn (fun t => f t x) (Icc 0 T) :=
  hc.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht,mem_univ x⟩)

theorem integral_continuous {f : ℝ → Space → ℝ} {T : ℝ}
    (hc : ContinuousOn (uncurry f) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun t => ∫ x, f t x ∂measure) (Icc 0 T) := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod
    (isCompact_Icc : IsCompact (Icc (0 : Space) 1))).exists_bound_of_continuousOn
    (hc.mono (prod_mono Subset.rfl (subset_univ _)))
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro t ht
    exact (continuous_slice hc ht).aestronglyMeasurable
  · intro t ht
    exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx => hC (t,x) ⟨ht,hx⟩)
  · exact integrable_const C
  · exact ae_of_all _ (fun x => continuous_time hc x)

theorem integral_hasDerivAt {f df : ℝ → Space → ℝ} {T t : ℝ}
    (hc : ContinuousOn (uncurry f) (Icc 0 T ×ˢ univ))
    (hdc : ContinuousOn (uncurry df) (Icc 0 T ×ˢ univ))
    (hd : ∀ s ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun r => f r x) (df s x) (Icc 0 T) s)
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun t => ∫ x, f t x ∂measure) (∫ x, df t x ∂measure) t := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod
    (isCompact_Icc : IsCompact (Icc (0 : Space) 1))).exists_bound_of_continuousOn
    (hdc.mono (prod_mono Subset.rfl (subset_univ _)))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := measure)
    (s := Ioo 0 T) (F := f) (F' := df) (bound := fun _ => C) (Ioo_mem_nhds ht.1 ht.2)
    (by filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
        exact (continuous_slice hc ⟨hr.1.le,hr.2.le⟩).aestronglyMeasurable)
    (integrable_continuous (continuous_slice hc ⟨ht.1.le,ht.2.le⟩))
    (continuous_slice hdc ⟨ht.1.le,ht.2.le⟩).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        intro r hr
        exact hC (r,x) ⟨⟨hr.1.le,hr.2.le⟩,hx⟩)
    (integrable_const C)
    (ae_of_all _ (fun x r hr => (hd r ⟨hr.1.le,hr.2.le⟩ x).hasDerivAt
      (Icc_mem_nhds hr.1 hr.2)))
  exact hh.2

end VelocityDetection.TorusClass
end

end OAI

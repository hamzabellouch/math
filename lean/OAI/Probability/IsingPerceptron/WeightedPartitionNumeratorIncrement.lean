import Mathlib
import OAI.Probability.IsingPerceptron.MarkedPartitionNumerator

namespace OAI

/-! Weighted Partition Numerator Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {E : Type} [MeasurableSpace E] [Nonempty E]

theorem weightedPartitionNumerator_increment {b l : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] {a : E → ℝ≥0∞} (ha : Measurable a)
    (hfin : ∀ᵐ y ∂μ, a y < ∞) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) {d k : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (F : Fin d → E → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (z : Fin k → ℝ) (hl : l < ∑ i, m i) (r : Fin d) :
    weightedPartitionNumerator b l μ a (Function.update m r (m r+1)) F z =
      ENNReal.ofReal ((m r-b)/((∑ i, m i)-l)) * weightedPartitionNumerator b l μ a m F z := by
  have hmu : ∀ i, b < Function.update m r (m r+1) i := by
    intro i
    by_cases hi : i = r
    · subst i
      rw [Function.update_self]
      linarith [hm r]
    · rw [Function.update_of_ne hi]
      exact hm i
  have hlu : l < ∑ i, Function.update m r (m r+1) i := by
    rw [sum_increment_entry]
    linarith
  rw [weightedPartitionNumerator_eq hb hb1 μ ha hfin hpos hpay _ hmu F hF z hlu,
    weightedPartitionNumerator_eq hb hb1 μ ha hfin hpos hpay m hm F hF z hl,
    partitionCoefficient_increment hb m hm hl r]
  ring

theorem weightedPartitionNumerator_descendant_congr {b l : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] {a : E → ℝ≥0∞} (ha : Measurable a)
    (hfin : ∀ᵐ y ∂μ, a y < ∞) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) {d k : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (F G : Fin d → E → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (z : Fin k → ℝ) (hl : l < ∑ i, m i) (r : Fin d) (c : ℝ≥0∞)
    (he : ∀ i, (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * G i y ∂μ) =
      if i = r then c * ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ
      else ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ) :
    weightedPartitionNumerator b l μ a m G z = c * weightedPartitionNumerator b l μ a m F z := by
  classical
  rw [weightedPartitionNumerator_eq hb hb1 μ ha hfin hpos hpay m hm G hG z hl,
    weightedPartitionNumerator_eq hb hb1 μ ha hfin hpos hpay m hm F hF z hl]
  have hp : (∏ i, ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * G i y ∂μ) =
      c * ∏ i, ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) * F i y ∂μ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r), he r, ite_eq_left rfl]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    rw [mul_assoc]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [he i, ite_eq_right (Finset.mem_erase.mp hi).1]
  rw [hp]
  ring

def poissonFiberIntegral (μ : Measure E) [SigmaFinite μ] (π : E → ℝ)
    (H : E × E × Measure E → ℝ≥0∞) (p : E × Measure E) : ℝ≥0∞ :=
  ∫⁻ y, if π y = π p.1 then H (p.1,y,p.2) else 0 ∂sigmaPart μ p.2

omit [Nonempty E] in
lemma measurable_poissonFiberIntegral (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π) {H : E × E × Measure E → ℝ≥0∞}
    (hH : Measurable H) : Measurable (poissonFiberIntegral μ π H) := by
  unfold poissonFiberIntegral
  apply measurable_sigmaPart_param μ measurable_snd
    (F := fun p : (E × Measure E) × E => if π p.2 = π p.1.1 then H (p.1.1,p.2,p.1.2) else 0)
  exact Measurable.ite (measurableSet_eq_fun (hπ.comp measurable_snd)
    (hπ.comp (measurable_fst.comp measurable_fst)))
    (hH.comp (by fun_prop)) measurable_const

lemma poissonLaw_fiber_null (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π) (hd : ∀ z, μ {y | π y = z} = 0) (x : E) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ y ∂ν, π y ≠ π x := by
  apply poissonLaw_ae_intensity μ (measurableSet_eq_fun hπ measurable_const).compl
  apply ae_iff.mpr
  simpa only [mem_ofPred_eq, not_not] using hd (π x)

lemma poissonFiberIntegral_insert (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π) (hd : ∀ z, μ {y | π y = z} = 0)
    {H : E × E × Measure E → ℝ≥0∞} (hH : Measurable H) (x : E) :
    ∀ᵐ ν ∂poissonLaw μ,
      poissonFiberIntegral μ π H (x,Measure.dirac x + ν) = H (x,x,Measure.dirac x + ν) := by
  filter_upwards [Marked.poissonGood_ae μ, poissonLaw_fiber_null μ hπ hd x] with ν hν hx
  rw [poissonFiberIntegral, Marked.sigmaPart_eq_of_good μ (hν.dirac_add x), lintegral_add_measure]
  have hm : Measurable (fun y => if π y = π x then H (x,y,Measure.dirac x + ν) else 0) :=
    Measurable.ite (measurableSet_eq_fun hπ measurable_const) (hH.comp (by fun_prop)) measurable_const
  rw [lintegral_dirac' _ hm]
  simp only [ite_true]
  have hz : (∫⁻ y, if π y = π x then H (x,y,Measure.dirac x+ν) else 0 ∂ν) = 0 := by
    calc
      _ = ∫⁻ y, (0 : ℝ≥0∞) ∂ν := lintegral_congr_ae (hx.mono fun y hy => ite_eq_right hy)
      _ = 0 := by simp
  rw [hz, add_zero]

theorem poissonFiberIntegral_eq_ae (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π) (hd : ∀ z, μ {y | π y = z} = 0)
    {H : E × E × Measure E → ℝ≥0∞} (hH : Measurable H) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ x ∂ν,
      poissonFiberIntegral μ π H (x,ν) = H (x,x,ν) := by
  let F : E × Measure E → ℝ≥0∞ := fun p =>
    if poissonFiberIntegral μ π H p = H (p.1,p.1,p.2) then 0 else 1
  have hF : Measurable F := Measurable.ite
    (measurableSet_eq_fun (measurable_poissonFiberIntegral μ hπ hH) (hH.comp (by fun_prop)))
    measurable_const measurable_const
  have hz : (∫⁻ ν, ∫⁻ x, F (x,ν) ∂ν ∂poissonLaw μ) = 0 := by
    rw [poissonLaw_insertion μ hF]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro x
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [poissonFiberIntegral_insert μ hπ hd hH x] with ν hν
    exact ite_eq_left hν
  have hn := (lintegral_eq_zero_iff' (poissonLaw_campbell_aemeasurable μ hF)).mp hz
  filter_upwards [hn] with ν hν
  have hx := (lintegral_eq_zero_iff (hF.comp (measurable_id.prodMk measurable_const))).mp hν
  filter_upwards [hx] with x hx
  by_contra hh
  have : (1 : ℝ≥0∞) = 0 := by simpa only [F, Function.comp_apply, id_eq, Pi.zero_apply, ite_eq_right hh] using hx
  exact one_ne_zero this

end IsingPerceptron

namespace IsingPerceptron
variable (A : Type) [MeasurableSpace A]

@[reducible] def noiseTreeSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit, inferInstance⟩
  | n+1 => let T := noiseTreeSpace n
    letI := T.space
    ⟨Measure (ℝ × (A × T.carrier)), inferInstance⟩

abbrev NoiseTree (n : ℕ) := (noiseTreeSpace A n).carrier
instance noiseTreeMeasurableSpace (n : ℕ) : MeasurableSpace (NoiseTree A n) := (noiseTreeSpace A n).space
instance noiseTreeNonempty : (n : ℕ) → Nonempty (NoiseTree A n)
  | 0 => ⟨PUnit.unit⟩
  | _+1 => ⟨0⟩

variable [Nonempty A]

def noiseCascadeLaw : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) → ProbabilityMeasure (NoiseTree A n)
  | 0, _, _ => ⟨Measure.dirac PUnit.unit, by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit))
      infer_instance⟩
  | n+1, b, μ => ⟨poissonLaw ((powerIntensity (b 0)).prod
      ((μ 0 : Measure A).prod (noiseCascadeLaw n (fun j => b (j+1)) (fun j => μ (j+1))))), by
        change IsProbabilityMeasure (poissonLaw _)
        infer_instance⟩

lemma noiseCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) := rfl

def noiseTreeForget : (n : ℕ) → NoiseTree A n → RawTree n
  | 0, _ => PUnit.unit
  | n+1, ν => ν.map (fun p => (p.1, noiseTreeForget n p.2.2))

omit [Nonempty A] in
lemma measurable_noiseTreeForget (n : ℕ) : Measurable (noiseTreeForget A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_map _ (measurable_fst.prodMk (ih.comp (measurable_snd.comp measurable_snd)))

lemma noiseCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeForget A n) = rawCascadeLaw n b := by
  induction n generalizing b μ with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw _).map (fun ν => ν.map (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))) = _
    rw [poissonLaw_map _ (T := fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))
      (measurable_fst.prodMk
      ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd)))]
    apply poissonLaw_congr
    have he : (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2)) =
        Prod.map id (fun q : A × NoiseTree A n => noiseTreeForget A n q.2) := rfl
    rw [he, ← Measure.map_prod_map _ _ (f := id)
      (g := fun q : A × NoiseTree A n => noiseTreeForget A n q.2) measurable_id
      ((measurable_noiseTreeForget A n).comp measurable_snd), Measure.map_id]
    congr 1
    change (((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))).map
        (noiseTreeForget A n ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_noiseTreeForget A n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]

def noiseTreeTotal (n : ℕ) (ν : NoiseTree A n) : ℝ≥0∞ := rawTreeTotal n (noiseTreeForget A n ν)

omit [Nonempty A] in
lemma measurable_noiseTreeTotal (n : ℕ) : Measurable (noiseTreeTotal A n) :=
  (measurable_rawTreeTotal n).comp (measurable_noiseTreeForget A n)

omit [Nonempty A] in
lemma noiseTreeTotal_succ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseTreeTotal A (n+1) ν = ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 ∂ν := by
  change (∫⁻ p, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
    ∂ν.map (fun p => (p.1,noiseTreeForget A n p.2.2))) = _
  rw [lintegral_map]
  · rfl
  · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd)
  · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd))

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_map_sigmaPart_param {E F P : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace P] (μ : Measure E) [SigmaFinite μ]
    {N : P → Measure E} (hN : Measurable N) {G : P × E → F} (hG : Measurable G) :
    Measurable (fun p => (sigmaPart μ (N p)).map (fun x => G (p,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun p : P × E => s.indicator (1 : F → ℝ≥0∞) (G p)) :=
    (measurable_const.indicator hs).comp hG
  convert measurable_sigmaPart_param μ hN hf using 1
  funext p
  rw [Measure.map_apply (f := fun x => G (p,x))
    (hG.comp (measurable_const.prodMk measurable_id)) hs]
  exact (lintegral_indicator_one (hs.preimage
    (hG.comp (measurable_const.prodMk measurable_id)))).symm

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTreeDisplace : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → RawTree n
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n+1, b, μ, c, u, s, ν =>
    (sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) ν).map
      (fun p => (c 0 (s,p.2.1) * p.1,
        noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2))

lemma measurable_noiseTreeDisplace (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeDisplace n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeDisplace
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1,
          noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2))
    have hs : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.1.1) := by fun_prop
    have ha : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.1) := by fun_prop
    have hx : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.1) := by fun_prop
    have hv : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.2) := by fun_prop
    exact (((hc 0).comp (hs.prodMk ha)).mul hx).prodMk
      ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (hs.prodMk ha)).prodMk hv))

end IsingPerceptron

namespace IsingPerceptron

lemma map_powerIntensity_subtree {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) (Q : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    (hm : (∫⁻ a, ENNReal.ofReal (c a ^ b) ∂μ) = 1)
    {T : A × B → C} (hT : Measurable T)
    (hLaw : ∀ a, P.map (fun v => T (a,v)) = Q) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) = (powerIntensity b).prod Q := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) :=
    ((hc.comp (measurable_fst.comp measurable_snd)).mul measurable_fst).prodMk
      (hT.comp measurable_snd)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF, lintegral_prod
    (fun p : ℝ × (A × B) => f (c p.2.1*p.1,T p.2)) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : A) :
      (∫⁻ v, f (c a*x,T (a,v)) ∂P) = ∫⁻ w, f (c a*x,w) ∂Q := by
    rw [← hLaw a, lintegral_map]
    · exact hf.comp (measurable_const.prodMk measurable_id)
    · exact hT.comp (measurable_const.prodMk measurable_id)
  have hp (x : ℝ) : (∫⁻ v : A × B, f (c v.1*x,T v) ∂μ.prod P) =
      ∫⁻ a, ∫⁻ w, f (c a*x,w) ∂Q ∂μ := by
    rw [lintegral_prod (fun v : A × B => f (c v.1*x,T v))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hv]
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × A => ∫⁻ w, f (c p.2*p.1,w) ∂Q) :=
    (hf.comp ((((hc.comp (measurable_snd.comp measurable_fst)).mul
      (measurable_fst.comp measurable_fst))).prodMk measurable_snd)).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : A) : (∫⁻ x, ∫⁻ w, f (c a*x,w) ∂Q ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) * (∫⁻ x, ∫⁻ w, f (x,w) ∂Q ∂powerIntensity b) := by
    rw [← lintegral_map hf.lintegral_prod_right' (measurable_const_mul (c a)),
      map_powerIntensity_mul (hcpos a), lintegral_smul_measure]
    rfl
  simp_rw [hx]
  rw [lintegral_mul_const _ (by fun_prop), hm, one_mul,
    ← lintegral_prod _ hf.aemeasurable]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_law (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeDisplace n b μ c u s) =
      rawCascadeLaw n b := by
  induction n generalizing b μ c u s with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let P : Measure (NoiseTree A n) := noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))
    let Q : Measure (RawTree n) := rawCascadeLaw n (fun j => b (j+1))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let G : A × NoiseTree A n → RawTree n := fun p =>
      noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2
    have hG : Measurable G :=
      (measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hGLaw (a : A) : P.map (fun v => G (a,v)) = Q :=
      ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))
        (fun i => hcpos (i+1)) (fun i => hm (i+1)) (u 0 (s,a))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n :=
      fun p => (c 0 (s,p.2.1) * p.1,G p.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).mul
        measurable_fst).prodMk (hG.comp measurable_snd)
    have hI : I.map T = (powerIntensity (b 0)).prod Q :=
      map_powerIntensity_subtree (b 0) (μ 0 : Measure A) P Q (c := fun a => c 0 (s,a))
        ((hc 0).comp (measurable_const.prodMk measurable_id)) (hcpos 0 s) (hm 0 s) hG hGLaw
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod Q)
    calc
      _ = (poissonLaw I).map (fun ν => ν.map T) := by
        apply Measure.map_congr
        filter_upwards [sigmaPart_eq_ae I] with ν hν
        change (sigmaPart I ν).map T = ν.map T
        rw [hν]
      _ = poissonLaw (I.map T) := poissonLaw_map I hT
      _ = _ := poissonLaw_congr hI

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_of_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hi : Integrable (fun x => (f x)^2) P) : Integrable f P := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' hf.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  change |f x| ≤ 1+(f x)^2
  have h := sq_nonneg (|f x|-1)
  nlinarith [sq_abs (f x)]

lemma integral_difference_same_law {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (hXL : P.map X = Q) (hYL : P.map Y = Q)
    {g : E → ℝ} (hg : Measurable g) (hg2 : Integrable (fun v => (g v)^2) Q) :
    Integrable (fun ω => g (X ω)-g (Y ω)) P ∧
    (∫ ω, g (X ω)-g (Y ω) ∂P) = 0 ∧
    Integrable (fun ω => (g (X ω)-g (Y ω))^2) P ∧
    (∫ ω, (g (X ω)-g (Y ω))^2 ∂P) ≤ 4 * ∫ v, (g v)^2 ∂Q := by
  have hX2 : Integrable (fun ω => (g (X ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hX.aemeasurable).mp
    rw [hXL]
    exact hg2
  have hY2 : Integrable (fun ω => (g (Y ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hY.aemeasurable).mp
    rw [hYL]
    exact hg2
  have hXi : Integrable (fun ω => g (X ω)) P := integrable_of_square P (hg.comp hX) hX2
  have hYi : Integrable (fun ω => g (Y ω)) P := integrable_of_square P (hg.comp hY) hY2
  have hdiff : Integrable (fun ω => (g (X ω)-g (Y ω))^2) P := by
    apply ((hX2.add hY2).const_mul 2).mono'
      (((hg.comp hX).sub (hg.comp hY)).pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (g (X ω)-g (Y ω))^2 ≤ 2*((g (X ω))^2+(g (Y ω))^2)
    nlinarith [sq_nonneg (g (X ω)+g (Y ω))]
  refine ⟨hXi.sub hYi, ?_, hdiff, ?_⟩
  · rw [integral_sub hXi hYi, ← integral_map hX.aemeasurable hg.aestronglyMeasurable,
      ← integral_map hY.aemeasurable hg.aestronglyMeasurable, hXL, hYL, sub_self]
  · calc
      _ ≤ ∫ ω, 2*((g (X ω))^2+(g (Y ω))^2) ∂P :=
        integral_mono hdiff ((hX2.add hY2).const_mul 2) (fun ω => by
          nlinarith [sq_nonneg (g (X ω)+g (Y ω))])
      _ = 4 * ∫ v, (g v)^2 ∂Q := by
        rw [integral_const_mul, integral_add hX2 hY2,
          ← integral_map hX.aemeasurable (hg.pow_const 2).aestronglyMeasurable,
          ← integral_map hY.aemeasurable (hg.pow_const 2).aestronglyMeasurable, hXL, hYL]
        ring

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_log_ratio (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let L := fun ν : NoiseTree A n =>
      Real.log (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
    Integrable L (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, L ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) = 0 ∧
    Integrable (fun ν => (L ν)^2) (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, (L ν)^2 ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact integral_difference_same_law (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    (rawCascadeLaw n b : Measure (RawTree n))
    (X := noiseTreeDisplace n b μ c u s) (Y := noiseTreeForget A n)
    ((measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id))
    (measurable_noiseTreeForget A n) (noiseTreeDisplace_law n b μ hc hu hcpos hm s)
    (noiseCascadeLaw_forget A n b μ)
    (Real.measurable_log.comp (measurable_rawTreeTotal n).ennreal_toReal)
    (rawCascade_total_log_square n b hb)

def noiseTreeFactor : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → ℝ≥0∞
  | 0, _, _, X, _, s, _ => ENNReal.ofReal (Real.exp (X 0 s))
  | n+1, b, μ, X, u, s, ν =>
    ∫⁻ p, ENNReal.ofReal (max p.1 0) *
      noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2
      ∂sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) ν

lemma measurable_noiseTreeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeFactor n b μ X u p.1 p.2) := by
  induction n generalizing b μ X u with
  | zero => exact (((hX 0).comp measurable_fst).exp).ennreal_ofReal
  | succ n ih =>
    unfold noiseTreeFactor
    apply measurable_sigmaPart_param _ measurable_snd
      (F := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        ENNReal.ofReal (max p.2.1 0) *
          noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)
    exact (by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
      (ℝ × (A × NoiseTree A n)) => ENNReal.ofReal (max p.2.1 0))).mul
        ((ih _ _ (fun i => hX (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop)))

theorem noiseTreeDisplace_total (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) =
      ENNReal.ofReal (Real.exp (-X 0 s)) * noiseTreeFactor n b μ X u s ν := by
  induction n generalizing b μ X u c s with
  | zero =>
    simp only [rawTreeTotal, noiseTreeFactor]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n := fun p =>
      (c 0 (s,p.2.1)*p.1,
        noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    change (∫⁻ p, ENNReal.ofReal (max p.1 0)*rawTreeTotal n p.2 ∂(sigmaPart I ν).map T) = _
    rw [lintegral_map]
    · change (∫⁻ p, ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
          rawTreeTotal n (T p).2 ∂sigmaPart I ν) = _
      have he (p : ℝ × (A × NoiseTree A n)) :
          ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) * rawTreeTotal n (T p).2 =
          ENNReal.ofReal (Real.exp (-X 0 s)) * (ENNReal.ofReal (max p.1 0) *
            noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
              (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by
        dsimp only [T]
        rw [ih _ _ (X := fun j => X (j+1)) (fun i => hc (i+1)) (fun i => hu (i+1)) (fun i => htel (i+1)),
          htel 0 s p.2.1]
        have hh (y x : ℝ) : max (Real.exp y*x) 0 = Real.exp y * max x 0 := by
          rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero]
        rw [hh, ENNReal.ofReal_mul (Real.exp_pos _).le]
        have hex (y z : ℝ) : ENNReal.ofReal (Real.exp (y-z)) * ENNReal.ofReal (Real.exp (-y)) =
            ENNReal.ofReal (Real.exp (-z)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
        calc
          _ = (ENNReal.ofReal (Real.exp (X 1 (u 0 (s,p.2.1))-X 0 s)) *
              ENNReal.ofReal (Real.exp (-X 1 (u 0 (s,p.2.1))))) *
              (ENNReal.ofReal (max p.1 0) *
                noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
                  (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by ring
          _ = _ := by rw [hex]
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd)
    · exact hT

lemma noiseTreeFactor_total_identity (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = ENNReal.ofReal (Real.exp (X 0 s)) *
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) := by
  rw [noiseTreeDisplace_total n b μ hc hu htel s ν, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem noiseCascade_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i))
    (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < noiseTreeFactor n b μ X u s ν ∧ noiseTreeFactor n b μ X u s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = X 0 s ∧
    Integrable (fun ν => (L ν-X 0 s)^2) P ∧
    (∫ ν, (L ν-X 0 s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  dsimp only
  let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
  let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
  let D := fun ν : NoiseTree A n => Real.log
      (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
  have hcpos : ∀ i s a, 0 < c i (s,a) := by intro i s a; rw [htel]; exact Real.exp_pos _
  have hT : Measurable (noiseTreeDisplace n b μ c u s) :=
    (measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id)
  have hgood : ∀ᵐ ν ∂P, 0 < rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) ∧
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) hT.aemeasurable
    rw [show P.map (noiseTreeDisplace n b μ c u s) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseTreeDisplace_law n b μ hc hu hcpos hm s]
    exact (rawCascade_total_moments n b hb).1
  have hden : ∀ᵐ ν ∂P, 0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) (measurable_noiseTreeForget A n).aemeasurable
    rw [show P.map (noiseTreeForget A n) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseCascadeLaw_forget A n b μ]
    exact (rawCascade_total_moments n b hb).1
  have he : L =ᵐ[P] fun ν => X 0 s + D ν := by
    filter_upwards [hgood, hden] with ν hν hνd
    have htpos := ENNReal.toReal_pos hν.1.ne' hν.2.ne
    have hdpos := ENNReal.toReal_pos hνd.1.ne' hνd.2.ne
    dsimp only [L, D]
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_div (mul_pos (Real.exp_pos _) htpos).ne' hdpos.ne',
      Real.log_mul (Real.exp_ne_zero _) htpos.ne', Real.log_exp]
    ring
  have h := noiseTreeDisplace_log_ratio n b hb μ hc hu hcpos hm s
  change Integrable D P ∧ (∫ ν, D ν ∂P) = 0 ∧ Integrable (fun ν => (D ν)^2) P ∧ _ at h
  have hi : Integrable L P := ((integrable_const (X 0 s)).add h.1).congr he.symm
  have hec : (fun ν => L ν-X 0 s) =ᵐ[P] D := by
    filter_upwards [he] with ν hν
    rw [hν]
    ring
  have he2 : (fun ν => (L ν-X 0 s)^2) =ᵐ[P] fun ν => (D ν)^2 :=
    hec.fun_comp (fun x : ℝ => x^2)
  refine ⟨?_, hi, ?_, h.2.2.1.congr he2.symm, ?_⟩
  · filter_upwards [hgood] with ν hν
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν]
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hν.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2⟩
  · rw [integral_congr_ae he, integral_add (integrable_const _) h.1, integral_const, h.2.1]
    simp [P]
  · rw [integral_congr_ae he2]
    exact h.2.2.2

end IsingPerceptron

end

end OAI

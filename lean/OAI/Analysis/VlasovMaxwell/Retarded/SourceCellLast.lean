import Mathlib
import OAI.Analysis.VlasovMaxwell.Continuation.DerivMovingEnergy
import OAI.Analysis.VlasovMaxwell.Flow.PhaseAcceleration

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Set

namespace RVM

def sourceCellLast (T len : ℝ) : ℕ := ⌊T/len⌋₊
def sourceCellLo (len : ℝ) (i : ℕ) : ℝ := i*len
def sourceCellHi (T len : ℝ) (i : ℕ) : ℝ := min T ((i+1:ℕ)*len)

def selectedSourceCells (T len a b r : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (sourceCellLast T len+1)).filter fun i =>
    sourceCellLo len i ≤ b ∧ a-r ≤ sourceCellHi T len i

lemma sourceCellLast_le {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len) :
    (sourceCellLast T len:ℝ)*len ≤ T := by
  exact (le_div_iff₀ hlen).mp (Nat.floor_le (div_nonneg hT hlen.le))

lemma sourceCell_mem_prefix {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ≤ sourceCellLast T len) :
    0 ≤ sourceCellLo len i ∧ sourceCellLo len i ≤ sourceCellHi T len i ∧
      sourceCellHi T len i ≤ T ∧ sourceCellHi T len i-sourceCellLo len i ≤ len := by
  have hil : (i:ℝ)*len ≤ T := (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hlen.le).trans
    (sourceCellLast_le hT hlen)
  have his : (i:ℝ) ≤ (i+1:ℕ) := by exact_mod_cast Nat.le_succ i
  have hull : (i:ℝ)*len ≤ (i+1:ℕ)*len := mul_le_mul_of_nonneg_right his hlen.le
  refine ⟨by dsimp [sourceCellLo]; positivity,le_min hil hull,min_le_left _ _,?_⟩
  have hh : sourceCellHi T len i ≤ (i:ℝ)*len+len := by
    unfold sourceCellHi
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using (min_le_right T ((i+1:ℕ)*len))
  dsimp [sourceCellLo]
  linarith

lemma sourceCell_full {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i < sourceCellLast T len) :
    sourceCellHi T len i-sourceCellLo len i=len := by
  have hh : ((i+1:ℕ):ℝ)*len ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hi) hlen.le).trans
      (sourceCellLast_le hT hlen)
  unfold sourceCellHi sourceCellLo
  rw [min_eq_right hh]
  push_cast
  ring

lemma sourceCell_cover {T len t : ℝ} (hlen : 0 < len) (ht : t ∈ Icc 0 T) :
    ∃ i ≤ sourceCellLast T len, t ∈ Icc (sourceCellLo len i) (sourceCellHi T len i) := by
  let i := ⌊t/len⌋₊
  have hi : i ≤ sourceCellLast T len := Nat.floor_mono ((div_le_div_iff_of_pos_right hlen).mpr ht.2)
  refine ⟨i,hi,?_,le_min ht.2 ?_⟩
  · exact (le_div_iff₀ hlen).mp (Nat.floor_le (div_nonneg ht.1 hlen.le))
  · have hh := Nat.lt_floor_add_one (t/len)
    apply le_of_lt
    have hf := (div_lt_iff₀ hlen).mp hh
    simpa only [Nat.cast_add,Nat.cast_one] using hf

lemma selectedSourceCells_cover {T len a b r : ℝ} (hlen : 0 < len) :
    Icc (max 0 (a-r)) (min T b) ⊆
      ⋃ i ∈ selectedSourceCells T len a b r, Icc (sourceCellLo len i) (sourceCellHi T len i) := by
  intro t ht
  obtain ⟨i,hi,htC⟩ := sourceCell_cover hlen ⟨(le_max_left _ _).trans ht.1,ht.2.trans (min_le_left _ _)⟩
  refine mem_iUnion₂.mpr ⟨i,?_,htC⟩
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    htC.1.trans (ht.2.trans (min_le_right _ _)),
    (le_max_right _ _).trans (ht.1.trans htC.2)⟩

lemma selectedSourceCells_subset_prefix {T len a b r : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ∈ selectedSourceCells T len a b r) :
    0 ≤ sourceCellLo len i ∧ sourceCellLo len i ≤ sourceCellHi T len i ∧
      sourceCellHi T len i ≤ T ∧ sourceCellHi T len i-sourceCellLo len i ≤ len := by
  classical
  exact sourceCell_mem_prefix hT hlen (by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega)

lemma selectedSourceCells_enlargement {T len a b r : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ∈ selectedSourceCells T len a b r) :
    Icc (sourceCellLo len i) (sourceCellHi T len i) ⊆
      Icc (max 0 (a-r-len)) (min T (b+len)) := by
  have hc := selectedSourceCells_subset_prefix hT hlen hi
  have hh := (Finset.mem_filter.mp hi).2
  intro t ht
  refine ⟨max_le (hc.1.trans ht.1) ?_,le_min (ht.2.trans hc.2.2.1) ?_⟩  <;> linarith [hc.2.2.2,hh.1,hh.2,ht.1,ht.2]

lemma sourceCells_pairwise_disjoint {T len : ℝ} (hlen : 0 < len) :
    Pairwise fun i j : ℕ => Disjoint
      (Ioc (sourceCellLo len i) (sourceCellHi T len i))
      (Ioc (sourceCellLo len j) (sourceCellHi T len j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  have hd (k : ℕ) : sourceCellHi T len k  ≤  ((k+1:ℕ):ℝ)*len := min_le_right _ _
  rcases lt_or_gt_of_ne hij with hh | hh
  · have hle : ((i+1:ℕ):ℝ)*len ≤ (j:ℝ)*len :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hh) hlen.le
    exact (not_lt_of_ge ((hi.2.trans (hd i)).trans hle)) hj.1
  · have hle : ((j+1:ℕ):ℝ)*len ≤ (i:ℝ)*len :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hh) hlen.le
    exact (not_lt_of_ge ((hj.2.trans (hd j)).trans hle)) hi.1

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

def goodFieldConeMass (s : Solution) (t : ℝ) (x : Vec) : ℝ≥0∞ :=
  ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
    ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,x-(t-r) • n.1))
      (s.B (r,x-(t-r) • n.1)) n.1^2) ∂sphereMeasure

def goodConeIntegrand (s : Solution) (t : ℝ) (x : Vec) (r : ℝ) (n : Sphere) : ℝ :=
  (t-r)^2 * goodConeDensity s (r,x-(t-r) • n.1) n.1

lemma EnergyPrefix.goodConeIntegrand_continuous {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    ContinuousOn (Function.uncurry (goodConeIntegrand s t x)) (Icc 0 t ×ˢ univ) :=
  EnergyPrefix.goodConeDensity_cone_continuous (hs.mono ht.2) ht.1 x

lemma EnergyPrefix.goodConeIntegrand_nonneg {s : Solution} {T t r : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (hr : r∈Icc 0 t) (x : Vec) (n : Sphere) :
    0≤goodConeIntegrand s t x r n :=
  mul_nonneg (sq_nonneg _) (EnergyPrefix.goodConeDensity_bounds (hs.mono ht.2) hr _ (sphere_norm n)).1

lemma EnergyPrefix.goodConeIntegrand_sphere_continuous {s : Solution} {T t r : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (hr : r∈Icc 0 t) (x : Vec) :
    Continuous (goodConeIntegrand s t x r) :=
  (hs.goodConeIntegrand_continuous ht x).comp_continuous
    (continuous_const.prodMk continuous_id) (fun n => ⟨hr,mem_univ n⟩)

lemma EnergyPrefix.goodConeIntegrand_sphere_integral_continuous {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    ContinuousOn (fun r => ∫ n : Sphere, goodConeIntegrand s t x r n ∂sphereMeasure) (Icc 0 t) := by
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ
    (hs.goodConeIntegrand_continuous ht x)
  exact fun r n _ hn => (hn (mem_univ n)).elim

lemma EnergyPrefix.goodConeIntegrand_lintegral_eq {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    (∫⁻ r in Icc 0 t, ∫⁻ n : Sphere, ENNReal.ofReal (goodConeIntegrand s t x r n) ∂sphereMeasure) =
      ENNReal.ofReal (∫ r in Icc 0 t, ∫ n : Sphere, goodConeIntegrand s t x r n ∂sphereMeasure) := by
  calc
    _ = ∫⁻ r in Icc 0 t, ENNReal.ofReal (∫ n : Sphere, goodConeIntegrand s t x r n ∂sphereMeasure) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro r hr
      exact (ofReal_integral_eq_lintegral_ofReal
        (integrableOn_univ.mp
          ((hs.goodConeIntegrand_sphere_continuous ht hr x).continuousOn.integrableOn_compact isCompact_univ))
        (ae_of_all _ (hs.goodConeIntegrand_nonneg ht hr x))).symm
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      ((hs.goodConeIntegrand_sphere_integral_continuous ht x).integrableOn_compact isCompact_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun r hr => integral_nonneg (hs.goodConeIntegrand_nonneg ht hr x)))).symm

lemma EnergyPrefix.goodFieldConeMass_le_density {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    goodFieldConeMass s t x ≤
      ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere, ENNReal.ofReal (goodConeIntegrand s t x r n) ∂sphereMeasure := by
  apply setLIntegral_mono' measurableSet_Icc
  intro r hr
  apply lintegral_mono
  intro n
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hp := EnergyPrefix.particle_cone_nonneg (hs.mono ht.2) hr (x-(t-r) • n.1) (sphere_norm n)
  dsimp [goodConeDensity,goodField]
  linarith

lemma EnergyPrefix.goodFieldConeMass_bound {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    goodFieldConeMass s t x ≤ ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  refine (hs.goodFieldConeMass_le_density ht x).trans ?_
  rw [hs.goodConeIntegrand_lintegral_eq ht x]
  apply ENNReal.ofReal_le_ofReal
  have hh := EnergyPrefix.goodConeDensity_time_integral_bound (hs.mono ht.2) ht.1 x
  simpa only [intervalIntegral.integral_of_le ht.1,integral_Icc_eq_integral_Ioc,goodConeIntegrand] using hh

lemma dyadicWindow_single_sum_indicator {α : Type*} (k : ℕ) (S : Finset ℕ)
    (G : ℕ → Set α) (p : α) (e : ℝ≥0∞) {x : ℝ}
    (hG : ∀ n∈S, p∈G n → DyadicWindow k n x) :
    (∑ n∈S, (G n).indicator (fun _ => e) p) ≤ (4*k+1 : ℕ)*e := by
  classical
  have hc : (S.filter (fun n => p∈G n)).card≤4*k+1 := by
    apply dyadicWindow_card_le
    intro n hn
    exact hG n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  have heq : (∑ n∈S, (G n).indicator (fun _ => e) p)=
      (S.filter (fun n => p∈G n)).card*e := by
    simp only [Set.indicator]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [heq]
  exact mul_le_mul' (by exact_mod_cast hc) le_rfl

lemma finset_sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑ i∈S, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑ i∈S, f i x ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

def receiverAngularSet (a : ℝ → Vec) (k j : ℕ) (t : ℝ) : Set Sphere :=
  {n | DyadicWindow k j (Real.sqrt ((1-dot n.1 (a t))/2))}

def goodFieldBinConeMass (s : Solution) (X a : ℝ → Vec) (k j : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
    (receiverAngularSet a k j t).indicator (fun n =>
      ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,X t-(t-r) • n.1))
        (s.B (r,X t-(t-r) • n.1)) n.1^2)) n ∂sphereMeasure

def goodFieldBudget (s : Solution) (X a : ℝ → Vec) (k : ℕ) (lo hi I : ℝ) (j : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi, goodFieldBinConeMass s X a k j t

lemma goodFieldBinConeMass_sum_le (s : Solution) (X a : ℝ → Vec)
    (k : ℕ) (S : Finset ℕ) (t : ℝ) :
    (∑ j∈S, goodFieldBinConeMass s X a k j t) ≤
      (4*k+1:ℕ)*goodFieldConeMass s t (X t) := by
  unfold goodFieldBinConeMass
  calc
    _ ≤ ∫⁻ r in Icc 0 t, ∑ j∈S, ∫⁻ n : Sphere,
        (receiverAngularSet a k j t).indicator (fun n =>
          ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,X t-(t-r) • n.1))
            (s.B (r,X t-(t-r) • n.1)) n.1^2)) n ∂sphereMeasure :=
      finset_sum_lintegral_le _ _ _
    _ ≤ ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
        (4*k+1:ℕ)*ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,X t-(t-r) • n.1))
          (s.B (r,X t-(t-r) • n.1)) n.1^2) ∂sphereMeasure := by
      apply lintegral_mono
      intro r
      refine (finset_sum_lintegral_le _ _ _).trans (lintegral_mono (fun n => ?_))
      exact dyadicWindow_single_sum_indicator k S (receiverAngularSet a k · t) n _
        (fun j _ hj => hj)
    _ = _ := by
      simp only [goodFieldConeMass,lintegral_const_mul' _ _ (by finiteness : ((4*k+1:ℕ):ℝ≥0∞)≠⊤)]

lemma EnergyPrefix.goodFieldBudget_sum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (S : Finset ℕ) :
    (∑ j∈S, goodFieldBudget s X a k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹ * (4*k+1:ℕ) * ENNReal.ofReal (hi-lo) *
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  unfold goodFieldBudget
  rw [← Finset.mul_sum]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi,
        (4*k+1:ℕ)*ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
      apply mul_le_mul' le_rfl
      refine (finset_sum_lintegral_le _ _ _).trans ?_
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact (goodFieldBinConeMass_sum_le s X a k S t).trans
        (mul_le_mul' le_rfl (hs.goodFieldConeMass_bound (hJ ht) (X t)))
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      ac_rfl

lemma EnergyPrefix.goodFieldBudget_tsum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹ * (4*k+1:ℕ) * ENNReal.ofReal (hi-lo) *
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (hs.goodFieldBudget_sum_bound X a k hJ)

lemma EnergyPrefix.goodFieldBudget_uniform {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) (hlen : hi-lo≤I) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j) ≤
      (4*k+1:ℕ)*ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  have hnorm : (ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo)≤1 := by
    calc
      _ ≤ (ENNReal.ofReal I)⁻¹*ENNReal.ofReal I :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlen)
      _ = 1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * (4*k+1:ℕ) * ENNReal.ofReal (hi-lo) *
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) :=
      hs.goodFieldBudget_tsum_bound X a k hJ
    _ = (4*k+1:ℕ)*((ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo))*
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by ac_rfl
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul' (mul_le_mul' le_rfl hnorm)
        (le_refl (ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y)))))

lemma EnergyPrefix.goodFieldBudget_finite {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j)≠⊤ := by
  apply ne_top_of_le_ne_top _ (hs.goodFieldBudget_tsum_bound X a k hJ)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hI).ne')
      (ENNReal.natCast_ne_top _)) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma EnergyPrefix.magnetic_lintegral_bound {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T) :
    (∫⁻ x : Vec, ENNReal.ofReal (‖s.B (t,x)‖^2)) ≤
      ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (EnergyPrefix.prefix_integrable_norm_sq hs.B_L2 ht)
    (ae_of_all _ (fun x => sq_nonneg ‖s.B (t,x)‖))]
  apply ENNReal.ofReal_le_ofReal
  rw [← (hs.mono ht.2).energy_conservation ht.1,← integral_const_mul]
  apply integral_mono (EnergyPrefix.prefix_integrable_norm_sq hs.B_L2 ht)
    ((hs.total_energy_integrable ht).const_mul 2)
  intro x
  dsimp only [totalEnergy]
  nlinarith [hs.particle_energy_nonneg ht x,sq_nonneg ‖s.E (t,x)‖]

def arrivalAngularSet (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k j : ℕ) : Set (ℝ × Vec) :=
  {p | (p∈arrivalDomain α zX T ∧
      DyadicWindow k j (Real.sqrt ((1-dot (arrivalDirection α zX T p)
        (arrivalVelocity α zX T p))/2))) ∨
    (p∈arrivalFinalDomain α zX T ∧
      DyadicWindow k j (Real.sqrt ((1-dot ((T-p.1)⁻¹ • ((α zX T).1-p.2))
        (velocity (α zX T).2))/2)))}

lemma PhaseFlowOn.measurable_arrivalAngularSet {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k j : ℕ) :
    MeasurableSet (arrivalAngularSet F.flow zX T k j) := by
  classical
  let U := arrivalDomain F.flow zX T
  let b : ℝ × Vec → ℝ := fun p => Real.sqrt ((1-dot
    (arrivalDirection F.flow zX T p) (arrivalVelocity F.flow zX T p))/2)
  have hb : ContinuousOn b U := by
    intro p hp
    exact (((continuousAt_const.sub (continuous_dot.continuousAt.comp ((F.arrivalDirection_continuousAt zX hp).prodMk
      (F.arrivalVelocity_continuousAt zX hp)))).div_const 2).sqrt).continuousWithinAt
  have hm : Measurable (U.indicator b) := hb.measurable_piecewise continuousOn_const
    (F.isOpen_arrivalDomain zX).measurableSet
  have hopen : MeasurableSet {p | p∈U ∧ DyadicWindow k j (b p)} := by
    convert (F.isOpen_arrivalDomain zX).measurableSet.inter
      ((measurableSet_dyadicWindow k j).preimage hm) using 1
    ext p
    change (p∈U ∧ DyadicWindow k j (b p)) ↔
      (p∈U ∧ DyadicWindow k j (U.indicator b p))
    by_cases hp : p∈U <;> simp [hp]
  have hfinal : MeasurableSet (arrivalFinalDomain F.flow zX T) :=
    (measurable_fst (measurableSet_Ioo)).inter
      (measurableSet_eq_fun (measurable_fst.add (measurable_const.sub measurable_snd).norm) measurable_const)
  have hbfinal : Measurable (fun p : ℝ × Vec => Real.sqrt ((1-dot
      ((T-p.1)⁻¹ • ((F.flow zX T).1-p.2)) (velocity (F.flow zX T).2))/2)) := by
    unfold dot
    fun_prop
  exact hopen.union (hfinal.inter ((measurableSet_dyadicWindow k j).preimage hbfinal))

lemma arrivalAngularSet_sum_indicator (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (S : Finset ℕ) (p : ℝ × Vec) (e : ℝ≥0∞) :
    (∑ j∈S, (arrivalAngularSet α zX T k j).indicator (fun _ => e) p) ≤
      (2*(4*k+1):ℕ)*e := by
  classical
  let G₁ : ℕ → Set (ℝ × Vec) := fun j =>
    {r | r∈arrivalDomain α zX T ∧ DyadicWindow k j (Real.sqrt ((1-dot
      (arrivalDirection α zX T r) (arrivalVelocity α zX T r))/2))}
  let G₂ : ℕ → Set (ℝ × Vec) := fun j =>
    {r | r∈arrivalFinalDomain α zX T ∧ DyadicWindow k j (Real.sqrt ((1-dot
      ((T-r.1)⁻¹ • ((α zX T).1-r.2)) (velocity (α zX T).2))/2))}
  have h₁ := dyadicWindow_single_sum_indicator k S G₁ p e (fun _ _ h => h.2)
  have h₂ := dyadicWindow_single_sum_indicator k S G₂ p e (fun _ _ h => h.2)
  have hpart (j : ℕ) : (arrivalAngularSet α zX T k j).indicator (fun _ => e) p ≤
      (G₁ j).indicator (fun _ => e) p+(G₂ j).indicator (fun _ => e) p := by
    by_cases hp : p∈arrivalAngularSet α zX T k j
    · rw [indicator_of_mem hp]
      rcases hp with h|h
      · rw [indicator_of_mem (show p∈G₁ j from h)]
        exact le_add_right le_rfl
      · rw [indicator_of_mem (show p∈G₂ j from h)]
        exact le_add_left le_rfl
    · rw [indicator_of_notMem hp]; exact zero_le
  calc
    _ ≤ ∑ j∈S, ((G₁ j).indicator (fun _ => e) p+(G₂ j).indicator (fun _ => e) p) :=
      Finset.sum_le_sum (fun j _ => hpart j)
    _ ≤ (4*k+1:ℕ)*e+(4*k+1:ℕ)*e := by
      rw [Finset.sum_add_distrib]
      exact add_le_add h₁ h₂
    _ = _ := by push_cast; ring

def magneticFieldBudget (s : Solution) (α : Phase → ℝ → Phase) (zX : Phase)
    (T : ℝ) (k : ℕ) (lo hi I : ℝ) (j : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi, ∫⁻ x : Vec,
    (arrivalAngularSet α zX T k j).indicator (fun p => ENNReal.ofReal (‖s.B p‖^2)) (t,x)

lemma EnergyPrefix.magneticFieldBudget_sum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (α : Phase → ℝ → Phase) (zX : Phase) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (S : Finset ℕ) :
    (∑ j∈S, magneticFieldBudget s α zX T k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹*(2*(4*k+1):ℕ)*ENNReal.ofReal (hi-lo)*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  unfold magneticFieldBudget
  rw [← Finset.mul_sum]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi, ∫⁻ x : Vec,
        (2*(4*k+1):ℕ)*ENNReal.ofReal (‖s.B (t,x)‖^2) := by
      apply mul_le_mul' le_rfl
      refine (finset_sum_lintegral_le _ _ _).trans ?_
      apply lintegral_mono
      intro t
      exact (finset_sum_lintegral_le _ _ _).trans
        (lintegral_mono (fun x => arrivalAngularSet_sum_indicator α zX T k S (t,x) _))
    _ ≤ (ENNReal.ofReal I)⁻¹ * ∫⁻ _t in Icc lo hi,
        (2*(4*k+1):ℕ)*ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [lintegral_const_mul' _ _ (by finiteness : ((2*(4*k+1):ℕ):ℝ≥0∞)≠⊤)]
      exact mul_le_mul' le_rfl (hs.magnetic_lintegral_bound (hJ ht))
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      ac_rfl

lemma EnergyPrefix.magneticFieldBudget_tsum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (α : Phase → ℝ → Phase) (zX : Phase) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) :
    (∑' j : ℕ, magneticFieldBudget s α zX T k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹*(2*(4*k+1):ℕ)*ENNReal.ofReal (hi-lo)*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (hs.magneticFieldBudget_sum_bound α zX k hJ)

lemma EnergyPrefix.magneticFieldBudget_uniform {s : Solution} {T lo hi I C : ℝ}
    (hs : EnergyPrefix s T) (α : Phase → ℝ → Phase) (zX : Phase) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) (hC : 0≤C) (hlen : hi-lo≤C*I) :
    (∑' j : ℕ, magneticFieldBudget s α zX T k lo hi I j) ≤
      (2*(4*k+1):ℕ)*ENNReal.ofReal C*ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  have hnorm : (ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo)≤ENNReal.ofReal C := by
    calc
      _ ≤ (ENNReal.ofReal I)⁻¹*ENNReal.ofReal (C*I) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlen)
      _ = _ := by
        rw [ENNReal.ofReal_mul hC,mul_left_comm,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top,mul_one]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹*(2*(4*k+1):ℕ)*ENNReal.ofReal (hi-lo)*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) :=
      hs.magneticFieldBudget_tsum_bound α zX k hJ
    _ = (2*(4*k+1):ℕ)*((ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo))*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hnorm) le_rfl

end RVM

end

end OAI

import Mathlib
import OAI.Analysis.HardSphere.Bridges.WienerGaussian
import OAI.Analysis.HardSphere.PathBounds.FreeVisitProbability

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.FreeVisits

lemma exp_block_sum_bound (C J : ℕ) (hC : 0<C) {η : ℝ} (hη : 0≤η) :
    ENNReal.ofReal (Real.exp (η*(J:ℝ))) ≤ 1 + ∑' k : ℕ,
      if C*k<J then ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) else 0 := by
  by_cases hJ : J=0
  · simp [hJ]
  · let k := (J-1)/C
    have hk : C*k<J := (Nat.mul_div_le (J-1) C).trans_lt (by omega)
    have hJle : J≤C*(k+1) := by
      have h:=Nat.lt_mul_div_succ (J-1) hC
      dsimp [k]
      omega
    have he : ENNReal.ofReal (Real.exp (η*(J:ℝ))) ≤
        ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hJle' : (J:ℝ)≤(C:ℝ)*((k:ℝ)+1) := by exact_mod_cast hJle
      nlinarith
    have hs : ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) ≤ ∑' j : ℕ,
        if C*j<J then ENNReal.ofReal (Real.exp (η*(C:ℝ)*((j:ℝ)+1))) else 0 := by
      simpa only [ite_eq_left hk] using (ENNReal.le_tsum (f:=fun j : ℕ ↦ if C*j<J then
        ENNReal.ofReal (Real.exp (η*(C:ℝ)*((j:ℝ)+1))) else 0) k)
    exact he.trans (hs.trans le_add_self)

lemma weighted_exp_tail_le (C k : ℕ) (η : ℝ) :
    Real.exp (η*(C:ℝ)*((k:ℝ)+1)) * (k:ℝ) *
      Real.exp (-(η*(C:ℝ)+2)*(k:ℝ)) ≤
    Real.exp (η*(C:ℝ)) * Real.exp (-1)^k := by
  rw [← Real.exp_nat_mul]
  have hk : (k:ℝ)≤Real.exp (k:ℝ) := by have := Real.add_one_le_exp (k:ℝ); linarith
  calc
    _ = (k:ℝ)*Real.exp (η*(C:ℝ)-2*(k:ℝ)) := by
      rw [mul_right_comm,mul_comm _ (k:ℝ),←Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (k:ℝ)*Real.exp (η*(C:ℝ)-2*(k:ℝ)) := mul_le_mul_of_nonneg_right hk (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

def expTailBound (C : ℕ) (η : ℝ) (a : ℝ≥0∞) : ℝ≥0∞ :=
  1+(ENNReal.ofReal (Real.exp (η*(C:ℝ)))+
       ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*(1-ENNReal.ofReal (Real.exp (-1)))⁻¹

lemma expTailBound_ne_top (C : ℕ) (η : ℝ) {a : ℝ≥0∞} (ha : a≠⊤) :
    expTailBound C η a≠⊤ := by
  have hr : ENNReal.ofReal (Real.exp (-1))<1 := by
    rw [ENNReal.ofReal_lt_one]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha⟩)
    (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hr).ne')⟩

lemma lintegral_exp_nat_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℕ) (hF : Measurable F)
    (C : ℕ) (hC : 0<C) {η : ℝ} (hη : 0≤η) (a : ℝ≥0∞)
    (htail : ∀ k : ℕ, 0<k → μ {w | C*k<F w} ≤
      (k:ℝ≥0∞)*a*ENNReal.ofReal (Real.exp (-(η*(C:ℝ)+2)*(k:ℝ)))) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (η*(F w:ℝ))) ∂μ ≤ expTailBound C η a := by
  classical
  let W : ℕ → Ω → ℝ≥0∞ := fun k ↦
    {w | C*k<F w}.indicator (fun _ ↦ ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))))
  have hW (k : ℕ) : Measurable (W k) := measurable_const.indicator
    (measurableSet_lt measurable_const hF)
  have hweight (index : ℕ) (sample : Ω) :
      W index sample = if C*index<F sample then
        ENNReal.ofReal (Real.exp (η*(C:ℝ)*((index:ℝ)+1))) else 0 := by
    by_cases hindex : C*index<F sample <;> simp [W,hindex]
  have hterm (k : ℕ) : (∫⁻ w,W k w ∂μ) ≤
      (ENNReal.ofReal (Real.exp (η*(C:ℝ)))+ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*
        ENNReal.ofReal (Real.exp (-1))^k := by
    rw [show (∫⁻ w,W k w ∂μ) = ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) * μ {w | C*k<F w} from
      lintegral_indicator_const (measurableSet_lt measurable_const hF) _]
    by_cases hk : k=0
    · subst k
      simpa only [Nat.cast_zero,zero_add,mul_one,pow_zero] using
        (mul_le_mul_right (prob_le_one (μ:=μ))
          (ENNReal.ofReal (Real.exp (η*(C:ℝ))))).trans (by simp)
    · have hb := htail k (Nat.pos_of_ne_zero hk)
      calc
        _ ≤ ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))) *
          ((k:ℝ≥0∞)*a*ENNReal.ofReal (Real.exp (-(η*(C:ℝ)+2)*(k:ℝ)))) := mul_le_mul_right hb _
        _ = a*ENNReal.ofReal (Real.exp (η*(C:ℝ)*((k:ℝ)+1))*(k:ℝ)*Real.exp (-(η*(C:ℝ)+2)*(k:ℝ))) := by
          simp only [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg k)),ENNReal.ofReal_natCast]
          ring
        _ ≤ a*ENNReal.ofReal (Real.exp (η*(C:ℝ))*Real.exp (-1)^k) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal (weighted_exp_tail_le C k η)) _
        _ ≤ _ := by
          rw [ENNReal.ofReal_mul (Real.exp_nonneg _),ENNReal.ofReal_pow (Real.exp_nonneg _)]
          calc
            _ = (ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*ENNReal.ofReal (Real.exp (-1))^k := by ring
            _ ≤ _ := by gcongr; exact le_add_self
  calc
    _ ≤ ∫⁻ w,1+∑' k,W k w ∂μ := lintegral_mono (fun w ↦ by
      simpa only [hweight] using exp_block_sum_bound C (F w) hC hη)
    _ = 1+∑' k,∫⁻ w,W k w ∂μ := by rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,lintegral_tsum (fun k ↦ (hW k).aemeasurable)]
    _ ≤ 1+∑' k,(ENNReal.ofReal (Real.exp (η*(C:ℝ)))+ENNReal.ofReal (Real.exp (η*(C:ℝ)))*a)*ENNReal.ofReal (Real.exp (-1))^k :=
      add_le_add_right (ENNReal.tsum_le_tsum hterm) _
    _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]; rfl

end HardSphere.FreeVisits

end

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.Lattice HardSphere.CellOrbital HardSphere.BathSlice
attribute [local irreducible] freeTrajectory pathVisitedSites

def visitWeight {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t η : ℝ) (X : Configuration n L) (w : CoordinatePaths n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (η*(visitCount L A i t X w:ℝ)))

lemma visitWeight_measurable {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    (t η : ℝ) (X : Configuration n L) : Measurable (visitWeight L A i t η X) :=
  ((measurable_const.mul ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp (visitCount_measurable L A i t X))).exp).ennreal_ofReal

lemma exp_nat_sum_le {a b c : ℕ} (h : a≤b+c) {η : ℝ} (hη : 0≤η) :
    ENNReal.ofReal (Real.exp (η*(a:ℝ))) ≤
      ENNReal.ofReal (Real.exp (η*(b:ℝ)))*ENNReal.ofReal (Real.exp (η*(c:ℝ))) := by
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h' : (a:ℝ)≤(b:ℝ)+(c:ℝ) := by exact_mod_cast h
  nlinarith

lemma visit_moment_add {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {s t η : ℝ} (hs : 0<s) (ht : 0<t) (hη : 0≤η) (p q : ℝ≥0∞)
    (hsbound : ∀ X, ∫⁻ w,visitWeight L A i s η X w ∂coordinateWiener n ≤p)
    (htbound : ∀ X, ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤q)
    (X : Configuration n L) :
    ∫⁻ w,visitWeight L A i (s+t) η X w ∂coordinateWiener n ≤p*q := by
  let F : CoordinatePaths n × CoordinatePaths n → ℝ≥0∞ := fun w ↦
    visitWeight L A i s η X w.1 * visitWeight L A i t η (freeTrajectory n L s w.1 X 1) w.2
  have hG : Measurable (fun w : CoordinatePaths n × CoordinatePaths n ↦
      visitWeight L A i t η (freeTrajectory n L s w.1 X 1) w.2) := by
    change Measurable (fun w : CoordinatePaths n × CoordinatePaths n ↦
      ENNReal.ofReal (Real.exp (η*((pathVisitedSites L (siteCenter L) A i
        (freeTrajectory n L t w.2 (freeTrajectory n L s w.1 X 1))).card:ℝ))))
    exact (measurable_const.mul ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp
      ((pathVisitedSites_card_measurable L (siteCenter L) A i).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable n L s t X))))).exp.ennreal_ofReal
  have hF : Measurable F := ((visitWeight_measurable L A i s η X).comp measurable_fst).mul hG
  calc
    _ ≤ ∫⁻ w,F (fun p ↦ normalizedPrefix (splitTime s t hs ht) (w p),
          fun p ↦ normalizedSuffix (splitTime s t hs ht) (w p)) ∂coordinateWiener n :=
      lintegral_mono (fun w ↦ exp_nat_sum_le (visit_count_split L A i hs ht w X) hη)
    _ = ∫⁻ w,F w ∂(coordinateWiener n).prod (coordinateWiener n) :=
      (coordinateSplit_preserving n (splitTime s t hs ht)
        (splitTime_pos s t hs ht) (splitTime_lt_one s t hs ht)).lintegral_comp hF
    _ = ∫⁻ w₁,∫⁻ w₂,F (w₁,w₂) ∂coordinateWiener n ∂coordinateWiener n :=
      lintegral_prod _ hF.aemeasurable
    _ ≤ ∫⁻ w₁,visitWeight L A i s η X w₁*q ∂coordinateWiener n := by
      apply lintegral_mono
      intro w₁
      dsimp only [F]
      rw [lintegral_const_mul _ (visitWeight_measurable L A i t η _)]
      exact mul_le_mul_right (htbound _) _
    _ = (∫⁻ w,visitWeight L A i s η X w ∂coordinateWiener n)*q :=
      lintegral_mul_const _ (visitWeight_measurable L A i s η X)
    _ ≤ p*q := mul_le_mul_left (hsbound X) _

lemma n_segment_visit_moment {n K : ℕ} (L : Length) (A : Finset (DiscreteTorus K)) (i : Fin n)
    {t η : ℝ} (ht : 0<t) (hη : 0≤η) (B : ℝ≥0∞)
    (hbound : ∀ X, ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤ B) :
    ∀ k : ℕ, 0<k → ∀ X,
      ∫⁻ w,visitWeight L A i ((k:ℝ)*t) η X w ∂coordinateWiener n ≤ B^k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa only [Nat.succ_eq_add_one,Nat.zero_add,Nat.cast_one,one_mul,pow_one] using hbound
  | succ k hk ih =>
    intro X
    have h := visit_moment_add L A i (mul_pos (by exact_mod_cast hk) ht) ht hη
      (B^k) B ih hbound X
    convert h using 1 <;> push_cast <;> ring_nf

lemma small_visit_moment {c : ℝ} (_hc : 0<c) {M : ℝ≥0∞}
    (htail : ∀ R : ℝ, 0≤R → wiener {w | R≤‖w‖}≤M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) {η t : ℝ} (hη : 0≤η) (ht : 0<t)
    (htsmall : t≤c/(2*(η*(29^3:ℝ)+2))) (X : Configuration n L) :
    ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤ expTailBound (29^3) η (3*M) := by
  apply lintegral_exp_nat_le (coordinateWiener n) (visitCount L A i t X)
    (visitCount_measurable L A i t X) (29^3) (by norm_num) hη (3*M)
  intro k hk
  have he : η*(29^3:ℝ)+2 ≤ c/(2*t) := by
    apply (le_div_iff₀ (by positivity : 0<2*t)).mpr
    have h := (le_div_iff₀ (by positivity : 0<2*(η*(29^3:ℝ)+2))).mp htsmall
    nlinarith
  have hexp : -c*(k:ℝ)/(2*t) ≤ -(η*(29^3:ℝ)+2)*(k:ℝ) := by
    calc
      _ = -(c/(2*t))*(k:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (neg_le_neg he) (Nat.cast_nonneg k)
  have hb := whole_time_visit_tail htail L hL A i ht k hk X
  apply hb.trans
  calc
    _ ≤ (k:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-(η*(29^3:ℝ)+2)*(k:ℝ)))) := by
      exact mul_le_mul_right (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)) _) _
    _ = _ := by norm_num only [Nat.cast_pow,Nat.cast_ofNat]; ring

theorem free_visit_moment (η₀ : ℝ) (hη₀ : 0≤η₀) :
    ∃ B : ℝ≥0∞, B<⊤ ∧ ∀ {n K : ℕ} [NeZero K], ∀ (L : Length), L.val=(K:ℝ) →
      ∀ (A : Finset (DiscreteTorus K)) (i : Fin n) (t η : ℝ),
        0<t → t≤2 → η≤η₀ → ∀ X : Configuration n L,
        ∫⁻ w,visitWeight L A i t η X w ∂coordinateWiener n ≤ B := by
  obtain ⟨c,M,hc,hM,htail⟩ := wiener_norm_gaussian_tail
  let τ : ℝ := c/(2*(η₀*(29^3:ℝ)+2))
  have hτ : 0<τ := div_pos hc (by positivity)
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (2/τ))
  have hm1 : (1:ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < m := by exact_mod_cast (lt_trans (by norm_num : (0:ℝ)<1) hm1)
  have hmpos' : (0:ℝ) < m := by exact_mod_cast hmpos
  have hτm : 2≤τ*(m:ℝ) := by
    have h := (le_max_right _ _).trans hm.le
    have h' := (div_le_iff₀ hτ).mp h
    nlinarith
  let B := expTailBound (29^3) η₀ (3*M)
  have hB : B≠⊤ := expTailBound_ne_top _ _ (ENNReal.mul_ne_top (by simp) hM.ne)
  refine ⟨B^m,lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top hB),?_⟩
  intro n K _ L hL A i t η ht ht2 hη X
  have hts : t/(m:ℝ)≤τ := (div_le_iff₀ hmpos').mpr (by nlinarith)
  have hs : ∀ X, ∫⁻ w,visitWeight L A i (t/(m:ℝ)) η₀ X w ∂coordinateWiener n ≤ B :=
    fun X ↦ small_visit_moment hc htail L hL A i hη₀ (div_pos ht hmpos') hts X
  have h := n_segment_visit_moment L A i (div_pos ht hmpos') hη₀ B hs m hmpos X
  have he : (m:ℝ)*(t/(m:ℝ))=t := mul_div_cancel₀ t (ne_of_gt hmpos')
  rw [he] at h
  apply le_trans _ h
  apply lintegral_mono
  intro w
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)))

end HardSphere.FreeVisits

end

end OAI

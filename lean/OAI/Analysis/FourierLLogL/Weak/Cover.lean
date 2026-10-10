import OAI.Analysis.FourierLLogL.Weak.Quantile

/-! # Amplification by translations. -/
noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL.Weak
open Real
open scoped Classical
variable {f : Torus → ℂ}

abbrev law : Measure Torus := circleMeasure

def offsetS (S : Set Torus) (z : Torus) := (fun x => z+x) ⁻¹' S
lemma offsetMeas {S : Set Torus} (h : MeasurableSet S) (z : Torus) :
    MeasurableSet (offsetS S z) := (measurable_const.add measurable_id) h

lemma flow (z : Torus) :
    MeasurePreserving (fun x => z+x) law law := by
  unfold law circleMeasure
  exact measurePreserving_add_left _ _

lemma volume_offset (S : Set Torus) (h : MeasurableSet S) (z : Torus) :
    law.real (offsetS S z)=law.real S := by
  unfold Measure.real offsetS
  rw [(flow z).measure_preimage h.nullMeasurableSet]

lemma offset_witness (S T : Set Torus) (hs : MeasurableSet S) (ht : MeasurableSet T) :
    ∃ z : Torus, law.real (S∩ offsetS T z) ≤ law.real S * law.real T := by
  let U : Set (Torus × Torus) := {p | p.2 ∈ S ∧ p.1+p.2∈T}
  have hU : MeasurableSet U := (measurable_snd hs).inter ((measurable_fst.add measurable_snd) ht)
  let f := U.indicator (fun _ => (1:ℝ))
  have hF : Integrable f (law.prod law) := (integrable_const _).indicator hU
  have H (z : Torus) :
      ∫ x : Torus, f (z,x) ∂law=law.real (S∩offsetS T z) := by
    rw [show (fun x : Torus => f (z,x))=(S∩offsetS T z).indicator (fun x => (1:ℝ)) from rfl,
      integral_indicator (hs.inter (offsetMeas ht z))]
    simp
  have he (x : Torus) :
      ∫ z : Torus, f (z,x) ∂law=S.indicator (fun x => law.real T) x := by
    by_cases hh : x∈S
    · rw [show (fun z : Torus => f (z,x)) = (offsetS T x).indicator (fun _ => (1:ℝ)) from by
        funext z; unfold offsetS f U; by_cases hi : z+x∈T <;> simp [hh,hi,add_comm x z],
        indicator_of_mem hh,integral_indicator (offsetMeas ht x)]
      simp [volume_offset T ht]
    rw [show (fun z : Torus => f (z,x))=(fun _ => 0) from by funext z; simp [f,U,hh],
      indicator_of_notMem hh]; simp
  have HV : ∫ z, (∫ x, f (z,x) ∂law) ∂law = law.real S*law.real T := by
    rw [integral_integral_swap (f:=fun i j => f (i,j)) hF, funext he, integral_indicator hs]
    simp
  obtain ⟨v,hv⟩ := exists_le_integral hF.integral_prod_left
  exact ⟨v,(H v) ▸ HV ▸ hv⟩

def spread (S : Set Torus) {n : ℕ} (f : Fin n → Torus) : Set Torus :=
    {x | ∃ i : Fin n, x∈offsetS S (f i)}

lemma spread_meas (S : Set Torus) {n : ℕ} (f : Fin n → Torus) (hS : MeasurableSet S) :
    MeasurableSet (spread S f) := by
  have h : spread S f= ⋃ i : Fin n,offsetS S (f i) := by ext x; simp [spread]
  rw [h]; exact MeasurableSet.iUnion fun i => offsetMeas hS _

lemma multiply_cloud (S : Set Torus) (h : MeasurableSet S) (n : ℕ) :
    ∃ z : Fin n → Torus, law.real (spread S z)ᶜ ≤ (law.real Sᶜ)^n := by
  induction n with
  | zero =>
    refine ⟨fun i => i.elim0,?_⟩
    rw [pow_zero]; exact measureReal_le_one
  | succ n ih =>
    obtain ⟨z,hz⟩ := ih
    obtain ⟨q,hq⟩ := offset_witness _ _ (spread_meas S z h).compl h.compl
    refine ⟨Fin.cons q z,?_⟩
    have HH : (spread S (Fin.cons q z))ᶜ=(spread S z)ᶜ ∩ offsetS Sᶜ q := by
      ext x
      have HI : x ∈ spread S (Fin.cons q z) ↔ x∈offsetS S q ∨ x∈spread S z := by
        constructor
        · rintro ⟨i,hi⟩
          refine Fin.cases ?_ ?_ i hi
          · intro H; exact Or.inl (by simpa using H)
          intro j h; right; exact ⟨j,by simpa using h⟩
        rintro (hh|⟨i,hi⟩)
        · exact ⟨0,by simpa using hh⟩
        exact ⟨i.succ,by simpa using hi⟩
      change x∉spread S (Fin.cons q z) ↔ x∉spread S z ∧ x∉offsetS S q
      rw [HI]; tauto
    rw [HH]; apply hq.trans
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right hz measureReal_nonneg

lemma clouds_fill (S : Set Torus) (h : MeasurableSet S) (hp : 0 < law.real S) :
    ∃ (n : ℕ), 0 < n ∧ ∃ f : Fin n → Torus, 1/2 ≤ law.real (spread S f) ∧
      (n:ℝ)*law.real S ≤ 4 := by
  let δ := law.real S
  let n : ℕ := Nat.floor (1/δ)+1
  have he : δ ≤ 1 := measureReal_le_one
  have hq : law.real Sᶜ = 1-δ := by rw [measureReal_compl h,probReal_univ]
  obtain ⟨z,hz⟩ := multiply_cloud S h n
  have HA : 1 ≤ (n:ℝ)*δ := by
    have he' := Nat.lt_floor_add_one (1/δ)
    unfold n; push_cast
    exact ((div_lt_iff₀ hp).mp he').le
  refine ⟨n,by unfold n; omega,z,?_,?_⟩
  · have H (n : ℕ) : (1+(n:ℝ)*δ)*(1-δ)^n ≤ 1 := by
      have hl : 0 ≤ 1-δ := by linarith
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [pow_succ]; push_cast
        have HE : (1+((n:ℝ)+1)*δ)*(1-δ) ≤ (1+(n:ℝ)*δ) := by
          nlinarith [Nat.cast_nonneg (α:=ℝ) n,mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (sq_nonneg δ)]
        nlinarith [mul_le_mul_of_nonneg_right HE (pow_nonneg hl n)]
    rw [measureReal_compl (spread_meas S z h),probReal_univ, hq] at hz
    nlinarith [H n, pow_nonneg (show 0 ≤ 1-δ by linarith) n]
  · have he' := Nat.floor_le (show 0 ≤ 1/δ by unfold δ; positivity)
    change (n:ℝ)*δ ≤ 4
    have hd : 0 < δ := hp
    unfold n; push_cast
    nlinarith [div_mul_cancel₀ 1 hd.ne',mul_le_mul_of_nonneg_right he' hd.le]

end FourierLLogL.Weak

end OAI

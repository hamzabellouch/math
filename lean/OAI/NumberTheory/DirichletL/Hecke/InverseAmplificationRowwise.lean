import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseMarked

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwisePolynomial

def logTest (W : ℝ→ℂ) : ℕ→ℝ→ℂ
  | 0 => W
  | n+1 => logProfile (logTest W n)

theorem logTest_support (W : ℝ→ℂ) (n : ℕ) :
    Function.support (logTest W n)⊆Function.support W := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (logProfile_support (logTest W n)).trans ih

theorem logTest_smooth (W : ℝ→ℂ) (n : ℕ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logTest W n) := by
  induction n with
  | zero => exact hW
  | succ n ih => exact logProfile_smooth (logTest W n) a b ha ((logTest_support W n).trans hs) ih

theorem no_slot_rowwise_endpoint
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ K : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (r : ℝ) (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb C T : ℝ) (σ freq : FreeRow→ℝ),
      0≤r → r≤R → 0≤C → 0≤T →
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc 0 1) → (∀ u∈rows, freq u∈Icc (-T) T) →
      (∀ n : ℕ, n≤2 → ∀ s∈Icc (0 : ℝ) 1, ∀ t∈Icc (-T) T,
        RawMoment data (twistProfile (logTest W n) s t) c κ C ∧
        RawMoment data (scaleProfile (twistProfile (logTest W n) s t)) c κ C) →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W (U^r) (σ u) (freq u)‖^2)≤
        12*(1+T)*(C*K*U^(sourceExponent r+ε)) := by
  obtain ⟨c,κ,K,hc,hc1,hκ,hK,he⟩ := no_slot_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a b B ha hab hB hφs hφB R ε hR hε
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he,eventually_ge_atTop (1 : ℝ)] with U he hU
  intro r data rows W wa wb C T σ freq hr hrR hC hT hwa hwb hWs hW hrows hσ hf hraw
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have henergy (n : ℕ) (hn : n≤2) (s : ℝ) (hs : s∈Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t∈Icc (-T) T) :
      ∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true (logTest W n) (U^r) s t‖^2≤
        C*K*U^(sourceExponent r+ε) := by
    have hlW := (logTest_support W n).trans hWs
    have htW := (twistProfile_support (logTest W n) s t).trans hlW
    have hlS := logTest_smooth W n wa wb hwa hWs hW
    have htS := twistProfile_smooth (logTest W n) s t wa wb hwa hlW hlS
    have hh := he r data rows (twistProfile (logTest W n) s t) wa wb C hr hrR hC
      hwa hwb htW htS hrows (hraw n hn s hs t ht).1 (hraw n hn s hs t ht).2
    simpa only [polynomial_twistProfile] using hh
  let Q := scaleSupport (Real.log (U^r)) wb
  have hcover : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/(U^r))≠0 → J∈Q := by
    simpa only [Real.exp_log hD] using scaleSupport_cover W wa wb (Real.log (U^r))
      (Real.log (U^r)) hwb hWs (le_refl _)
  have hh := HeckeDetectorRowwiseMarked.marked_rowwise rows
    (fun u : FreeRow => data.character ⟨u.val,u.property.1⟩) true W (U^r) hD Q hcover
    (fun _ => 1) 0 1 (-T) T (C*K*U^(sourceExponent r+ε)) (by norm_num) (by linarith)
    σ freq hσ hf
    (by simpa only [mul_one,logTest] using henergy 0 (by omega))
    (by simpa only [mul_one,logTest] using henergy 1 (by omega))
    (by simpa only [mul_one,logTest] using henergy 2 (by omega))
  simp only [mul_one] at hh
  refine hh.trans ?_
  have hE : 0≤C*K*U^(sourceExponent r+ε) := by positivity
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI

import Mathlib
import OAI.Probability.Ballisticity.Crossings.FirstLayerHitRecordPrefix
import OAI.Probability.Ballisticity.Estimates.JointPastRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma recordIndexPosition_prefix_coord {d : ℕ} (e : Direction d) (X Y : Path d)
    (h0 : X 0 = 0) (hD : X ∈ NoDrop (realPosition (step e)) 0)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) (n k : ℕ)
    (hk : (k : ℤ) ≤ signedHeight e (X n)) (hXY : ∀ j ≤ n, X j = Y j) :
    recordIndexPosition (realPosition (step e)) k X =
      recordIndexPosition (realPosition (step e)) k Y := by
  by_cases hz : k = 0
  · subst k
    simp only [recordIndexPosition,recordIndexTime_zero]
    exact hXY 0 (Nat.zero_le n)
  obtain ⟨m,hm⟩ := noDrop_firstLayerHit_exists e X h0 hnn ht (Nat.pos_of_ne_zero hz)
  have hmn : m ≤ n := by
    by_contra hh
    have hc := hm.2 n (by omega)
    omega
  have hr := firstLayerHit_recordPrefix e X h0 hD hnn (Nat.pos_of_ne_zero hz) hm
  have hr' := (recordIndexPrefix_prefix (realPosition (step e)) k m X Y
    (fun j hj => hXY j (hj.trans hmn))).mp hr
  simp only [recordIndexPosition,recordIndexTime_eq _ _ _ _ hr,recordIndexTime_eq _ _ _ _ hr']
  exact hXY m hmn

lemma regularPath_recenter {d : ℕ} (ℓ : Vector d) (x : Lattice d) (X : Path d)
    (hX : X ∈ RegularPath ℓ x) : (fun j => X j-x) ∈ RegularPath ℓ 0 := by
  refine ⟨by simp only [hX.1,sub_self],?_,?_⟩
  · intro n
    obtain ⟨f,hf⟩ := hX.2.1 n
    exact ⟨f,by dsimp only; rw [hf]; abel⟩
  · change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' TransientPaths ℓ
    rw [transientPaths_translation]
    exact hX.2.2

lemma noDrop_recenter {d : ℕ} (ℓ : Vector d) (x : Lattice d) (X : Path d)
    (hX : X ∈ NoDrop ℓ x) : (fun j => X j-x) ∈ NoDrop ℓ 0 := by
  change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' NoDrop ℓ 0
  rw [noDrop_translation]
  simpa only [add_zero] using hX

lemma trueRecord_recenter {d : ℕ} (ℓ : Vector d) (x : Lattice d) (X : Path d)
    (n : ℕ) (hn : TrueRecord ℓ X n) : TrueRecord ℓ (fun j => X j-x) n := by
  constructor
  · intro j hj
    dsimp only
    simp only [dot_realPosition_sub]
    exact sub_lt_sub_right (hn.1 j hj) _
  · intro j
    dsimp only
    simp only [dot_realPosition_sub]
    exact sub_le_sub_right (hn.2 j) _

lemma translated_recordIndexPosition_suffix {d : ℕ} (e : Direction d)
    (x : Lattice d) (X : Path d)
    (hX : X ∈ RegularPath (realPosition (step e)) x)
    (hD : X ∈ NoDrop (realPosition (step e)) x)
    (n H : ℕ) (hn : 0 < n) (htrue : TrueRecord (realPosition (step e)) X n)
    (hH : signedHeight e (X n) = signedHeight e x+H) (j : ℕ) :
    recordIndexPosition (realPosition (step e)) (j+H) (fun k => X k-x) =
      recordIndexPosition (realPosition (step e)) j (fun k => X (n+k)-X n)+(X n-x) := by
  let ℓ := realPosition (step e)
  let Z : Path d := fun k => X k-x
  have hZ : Z ∈ RegularPath ℓ 0 := regularPath_recenter ℓ x X hX
  have hZD := noDrop_recenter ℓ x X hD
  have hZT := trueRecord_recenter ℓ x X n htrue
  have hs (k : ℕ) : signedHeight e (Z (k+1)) ≤ signedHeight e (Z k)+1 := by
    obtain ⟨f,hf⟩ := hZ.2.1 k
    rw [hf]
    exact signedHeight_step_le e _ f
  have hc := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) Z hs hZT.1
  have hc' : recordCount ℓ Z n = H := by
    have h0 : signedHeight e (Z 0) = 0 := by rw [hZ.1]; simp [signedHeight]
    have hh : signedHeight e (Z n) = H := by dsimp [Z]; rw [signedHeight_sub,hH]; omega
    rw [h0,hh,zero_add] at hc
    exact_mod_cast hc.symm
  have hh := recordIndexPosition_suffix ℓ Z hZD hZ.2.2 hn hZT j
  rw [hc'] at hh
  convert hh using 2
  congr 1
  funext k
  dsimp [Z]
  abel

lemma boundaryData_firstHit_prefix {d : ℕ} (e : Direction d) (x y : Lattice d)
    (hxy : signedHeight e x = signedHeight e y) (H : ℕ) (P : Path d × Path d)
    (hX : P.1 ∈ RegularPath (realPosition (step e)) x)
    (hY : P.2 ∈ RegularPath (realPosition (step e)) y)
    (hD : P.1 ∈ NoDrop (realPosition (step e)) x)
    (hE : P.2 ∈ NoDrop (realPosition (step e)) y)
    (hb : BoundaryAt (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P
      (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).1
      (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).2)
    (j : ℕ) (hj : j ≤ H) :
    let F := boundaryData (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P
    recordIndexPosition (realPosition (step e)) j (fun k => P.1 k-x) =
      recordIndexPosition (realPosition (step e)) j (fun k => extendPrefix F.1.1 F.2.1 k-x) ∧
    recordIndexPosition (realPosition (step e)) j (fun k => P.2 k-y) =
      recordIndexPosition (realPosition (step e)) j (fun k => extendPrefix F.1.2 F.2.2 k-y) := by
  dsimp only
  let ℓ := realPosition (step e)
  let L := ((signedHeight e x+H : ℤ) : ℝ)
  let q := boundaryTimes ℓ L P
  have hh : signedHeight e x+H ≤ signedHeight e (P.1 q.1) := by
    have hh := hb.2.2.2.1
    rw [signedHeight_projection e] at hh
    exact_mod_cast hh
  have he : signedHeight e (P.1 q.1) = signedHeight e (P.2 q.2) := by
    have he := hb.2.2.1.2.2
    rw [signedHeight_projection e,signedHeight_projection e] at he
    exact_mod_cast he
  have hxr := regularPath_recenter ℓ x P.1 hX
  have hyr := regularPath_recenter ℓ y P.2 hY
  constructor
  · apply recordIndexPosition_prefix_coord e _ _ hxr.1 (noDrop_recenter ℓ x P.1 hD)
      hxr.2.1 hxr.2.2 q.1 j
    · simp only [signedHeight_sub]
      omega
    · intro k hk
      change k ≤ (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).1 at hk
      change P.1 k-x = extendPrefix q.1 (Preorder.frestrictLe q.1 P.1) k-x
      rw [extendPrefix_apply _ _ _ hk]
      rfl
  · apply recordIndexPosition_prefix_coord e _ _ hyr.1 (noDrop_recenter ℓ y P.2 hE)
      hyr.2.1 hyr.2.2 q.2 j
    · simp only [signedHeight_sub]
      omega
    · intro k hk
      change k ≤ (boundaryTimes (realPosition (step e)) ((signedHeight e x+H : ℤ) : ℝ) P).2 at hk
      change P.2 k-y = extendPrefix q.2 (Preorder.frestrictLe q.2 P.2) k-y
      rw [extendPrefix_apply _ _ _ hk]
      rfl

end DirectionalTransience

end

end

end OAI

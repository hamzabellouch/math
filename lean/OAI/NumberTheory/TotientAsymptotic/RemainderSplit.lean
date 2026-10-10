import OAI.NumberTheory.TotientAsymptotic.AttachTail
import OAI.NumberTheory.TotientAsymptotic.TailVolume

namespace OAI

/-! Exact separation of the prime prefix from its discrete tail thresholds. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primePrefixCoord {J : ℕ} (p : Fin J → ℕ) : Fin J → ℝ :=
  fun i => Real.log (Real.log (p i : ℝ))

lemma extractTail_D {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hPH : P H ≤ H) (hHm : H ≤ m x) (hh : H ≤ h) (hhm : h ≤ m x) :
    D h (extractTail x H η) =
      ∑ r ∈ Finset.Icc (R x H+1) (L x H), a (r-(m x-h))*remainderCoord x η r := by
  unfold D
  apply Finset.sum_bij (fun l _ => m x-l)
  · intro l hl
    have := Finset.mem_Ico.mp hl
    apply Finset.mem_Icc.mpr
    unfold R L
    omega
  · intro l hl k hk he
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    refine ⟨m x-r, ?_, ?_⟩
    · apply Finset.mem_Ico.mpr
      unfold R L at hr'
      omega
    · unfold L at hr'
      omega
  · intro l hl
    rw [extractTail_log η hHm hl]
    congr 2
    have := Finset.mem_Ico.mp hl
    omega

lemma sum_Icc_split_at {i R L : ℕ} (hi : i ≤ R) (hR : R ≤ L) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc (i+1) L, f r) =
      (∑ r ∈ Finset.Icc (i+1) R, f r) + ∑ r ∈ Finset.Icc (R+1) L, f r := by
  have he : Finset.Icc (i+1) L = Finset.Icc (i+1) R ∪ Finset.Icc (R+1) L := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [he, Finset.sum_union]
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have := Finset.mem_Icc.mp hr
  have := Finset.mem_Icc.mp hs
  omega

lemma prefix_sum_fin {J i : ℕ} (u : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc (i+1) J, a (r-i)*u r) =
      ∑ j : Fin J, if i < j.val+1 then a (j.val+1-i)*u (j.val+1) else 0 := by
  have hs : Finset.Icc (i+1) J = (Finset.Icc 1 J).filter (fun r => i < r) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  rw [hs, Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => j.val+1)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩
  · intro j _ k _ he
    apply Fin.ext
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨⟨r-1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro j _
    rfl

lemma remainder_prefix_coord {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H))
    (i : Fin (R x H)) :
    remainderCoord x η (i.val+1) =
      primePrefixCoord (fun j : Fin (R x H) => remainderPrime η (j.val+1)) i := by
  simp [remainderCoord, primePrefixCoord]

lemma remainder_sum_prefix_tail {x : ℝ} {H i : ℕ}
    (η : RemainderDatum (L x H)) (hPH : P H ≤ H) (hHm : H ≤ m x)
    (hi : i ≤ R x H) :
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r) =
      (∑ j : Fin (R x H), if i < j.val+1 then
        a (j.val+1-i)*remainderCoord x η (j.val+1) else 0) +
      D (m x-i) (extractTail x H η) := by
  have hRL : R x H ≤ L x H := by unfold R L; omega
  rw [sum_Icc_split_at hi hRL, prefix_sum_fin]
  congr 1
  have hmi : i ≤ m x := hi.trans (Nat.sub_le _ _)
  rw [extractTail_D η hPH hHm (by unfold R at hi; omega) (Nat.sub_le _ _),
    Nat.sub_sub_self hmi]

def perturbedTailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    Set (Fin (R x H) → ℝ) :=
  {u | (∀ i, D (m x-(i.val+1)) η ≤
      prefixLinear (R x H) u i + (xi x (i.val+1)-1)*u i) ∧
    (∑ i : Fin (R x H), a (i.val+1)*u i) ≤ xi x 0*B x-D (m x) η}

lemma basic_remainder_mem_perturbed {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hPH : P H < H) (hHm : H ≤ m x) :
    primePrefixCoord (fun i : Fin (R x H) => remainderPrime η (i.val+1)) ∈
      perturbedTailPrefixRegion x H (extractTail x H η) := by
  let u := primePrefixCoord (fun i : Fin (R x H) => remainderPrime η (i.val+1))
  have hRL : R x H < L x H := by unfold R L; omega
  constructor
  · intro i
    have hi : i.val+1 ≤ R x H := by have := i.isLt; omega
    have hib : i.val+1 ∈ Finset.Icc 0 (L x H) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have ht := hη.2.2.1 (i.val+1) hib
    rw [remainder_sum_prefix_tail η hPH.le hHm hi,
      ite_eq_right (by omega : i.val+1 ≠ L x H), remainder_prefix_coord] at ht
    have he : (∑ j : Fin (R x H), if i.val+1 < j.val+1 then
        a (j.val+1-(i.val+1))*remainderCoord x η (j.val+1) else 0) =
        u i-prefixLinear (R x H) u i := by
      rw [prefixLinear_apply]
      simp only [remainder_prefix_coord, Nat.add_lt_add_iff_right,
        Nat.add_sub_add_right, Fin.lt_def, u]
      ring
    rw [he] at ht
    change D (m x-(i.val+1)) (extractTail x H η) ≤
      prefixLinear (R x H) u i+(xi x (i.val+1)-1)*u i
    dsimp only [u] at ht
    nlinarith
  · have ht := hη.2.2.1 0 (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩)
    rw [remainder_sum_prefix_tail η hPH.le hHm (Nat.zero_le _),
      ite_eq_right (by omega : 0 ≠ L x H)] at ht
    have hz : remainderCoord x η 0 = B x := by simp [remainderCoord]
    rw [hz] at ht
    simpa only [Nat.zero_lt_succ, ite_true, Nat.sub_zero, remainder_prefix_coord]
      using (le_sub_iff_add_le.mpr ht)

end TotientAsymptotic

end

end OAI

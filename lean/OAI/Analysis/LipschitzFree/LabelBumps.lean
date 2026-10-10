import OAI.Analysis.LipschitzFree.AffineWeights

namespace OAI

/-!
# Lipschitz label bumps and affine mass estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

def labelBump (h : M → N) (a : N) (L K : ℝ) (t : M) : ℝ :=
  L * max (1 - dist a (h t) / K) 0

omit [MetricSpace M] in
theorem labelBump_nonneg (h : M → N) (a : N) {L K : ℝ} (hL : 0 ≤ L) (t : M) :
    0 ≤ labelBump h a L K t := mul_nonneg hL (le_max_right _ _)

omit [MetricSpace M] in
theorem labelBump_le (h : M → N) (a : N) {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (t : M) :
    labelBump h a L K t ≤ L := by
  unfold labelBump
  have hm : max (1-dist a (h t)/K) 0 ≤ 1 := max_le (by have := div_nonneg (dist_nonneg : 0 ≤ dist a (h t)) hK.le; linarith) (by norm_num)
  simpa using mul_le_mul_of_nonneg_left hm hL

omit [MetricSpace M] in
theorem labelBump_self (h : M → N) (a : N) {L K : ℝ} {t : M} (ht : h t = a) :
    labelBump h a L K t = L := by simp [labelBump, ht]

theorem labelBump_sub (h : M → N) (hh : LipschitzWith 1 h) (a : N)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (x y : M) :
    |labelBump h a L K x - labelBump h a L K y| ≤ (L/K) * dist x y := by
  unfold labelBump
  rw [← mul_sub, abs_mul, abs_of_nonneg hL]
  have hh' : dist (h x) (h y) ≤ dist x y := by simpa using hh.dist_le_mul x y
  calc
    _ ≤ L * |(1-dist a (h x)/K) - (1-dist a (h y)/K)| :=
      mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ 0) hL
    _ = (L/K) * |dist a (h x) - dist a (h y)| := by
      rw [show (1-dist a (h x)/K) - (1-dist a (h y)/K) =
        -(dist a (h x)-dist a (h y))/K by ring, abs_div, abs_neg, abs_of_pos hK]
      ring
    _ ≤ (L/K) * dist x y := mul_le_mul_of_nonneg_left
      ((show |dist a (h x) - dist a (h y)| ≤ dist (h x) (h y) by simpa only [dist_comm] using abs_dist_sub_le (h x) (h y) a).trans hh') (div_nonneg hL hK.le)

theorem labelBump_lipschitz (h : M → N) (hh : LipschitzWith 1 h) (a : N)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (hLK : L ≤ K) :
    LipschitzWith 1 (labelBump h a L K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  exact (labelBump_sub h hh a hL hK x y).trans
    (mul_le_of_le_one_left dist_nonneg ((div_le_one hK).mpr hLK))

omit [MetricSpace M] in
theorem labelBump_positive (h : M → N) (a : N) {L K : ℝ}
    (hL : 0 < L) (hK : 0 < K) {t : M} (ht : 0 < labelBump h a L K t) :
    dist a (h t) < K := by
  unfold labelBump at ht
  have hm : 0 < max (1-dist a (h t)/K) 0 := (mul_pos_iff_of_pos_left hL).mp ht
  have hs : dist a (h t)/K < 1 := by
    have hh := (lt_max_iff).mp hm
    rcases hh with hh | hh
    · linarith
    · exact False.elim (lt_irrefl (0 : ℝ) hh)
  exact (div_lt_one hK).mp hs

theorem affine_bump_mass (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (h : M → N) (hh : LipschitzWith 1 h) (x a : M) (ha : h a = h x)
    (L K p R : ℝ) (hL : 0 ≤ L) (hK : 0 < K) (hp : 0 ≤ p)
    (hn : ‖T‖ ≤ 2*p) (hR : dist x a ≤ R) (he : ‖T (delta o a) - delta o a‖ < 1) :
    L - (L/K)*(2*p*R+1) ≤
      pairing (affineWeights o sep S ho (T (delta o x)))
        (fun j : S => labelBump h (h x) L K j.val) := by
  let b := labelBump h (h x) L K
  have hb (s t : M) : |b s - b t| ≤ (L/K)*dist s t := labelBump_sub h hh (h x) hL hK s t
  let f := Lip0.center o b (L/K) (div_nonneg hL hK.le) hb
  have hfn : ‖f‖ ≤ L/K := Lip0.center_norm_le o b _ _ hb
  have hda : ‖T (delta o x) - delta o a‖ ≤ 2*p*R+1 := by
    calc
      _ = ‖T (delta o x - delta o a) + (T (delta o a) - delta o a)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖T (delta o x - delta o a)‖ + ‖T (delta o a) - delta o a‖ := norm_add_le _ _
      _ ≤ (2*p)*R + 1 := add_le_add
        ((T.le_opNorm _).trans (mul_le_mul hn (by simpa using hR) (norm_nonneg _) (by positivity))) he.le
  have heq := affineWeights_pairing o sep S ho (T (delta o x)) (hfixed _) b (L/K)
    (div_nonneg hL hK.le) hb
  have hba : b a = L := labelBump_self h (h x) ha
  have hpair : pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => b j.val) - L =
      dualPairing o f (T (delta o x) - delta o a) := by
    rw [heq, map_sub, dualPairing_delta]
    change _ = _ - (b a - b o)
    rw [hba]
    ring
  have heval := (dualPairing_bound o f (T (delta o x) - delta o a)).trans
    (mul_le_mul hda hfn (norm_nonneg _) ((norm_nonneg _).trans hda))
  rw [← hpair] at heval
  have hh := (abs_le.mp heval).1
  change L - _ ≤ pairing _ (fun j : S => b j.val)
  nlinarith

end DiscreteFree
end

end

end OAI

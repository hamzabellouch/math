import OAI.Analysis.FourierLLogL.Snapshot.Measure

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture
variable {M : ℕ} {α β : Type} [Fintype α] [Fintype β]
open scoped Classical

def rangeIx (m : ℕ) := 2^m
def precision (i m : ℕ) := 25+6*i+m
def sharp (i : ℕ) := side i ^6 / 32768
def portrait (b : Bool) (s : Scene M) (d : Finset (Grid M)) (i m : ℕ) :=
    hist s (sight s b d (precision i m))

def distance (f g : α → ℝ) := ∑ x, |f x-g x|

lemma sharp_pos (i : ℕ) : 0 < sharp i := div_pos (pow_pos (side_pos i) _) (by norm_num)

lemma coordinate_le (i m : ℕ) {n : ℕ} (h : n ≤ rangeIx m) :
    (n:ℝ)*(8*side (precision i m)) ≤ sharp i := by
  apply le_trans (b:= (2:ℝ)^m*(8*side (precision i m))) (by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast h)
      (by have := side_pos (precision i m); positivity))
  unfold precision sharp
  have heq : side (25+6*i+m) = side 25 * side i ^6 * side m := by
    simp [side,pow_add,pow_mul,mul_comm 6 i]
  rw [heq]
  rw [show (2:ℝ)^m * (8*(side 25 * side i^6 * side m))=
        (side m*(2:ℝ)^m) *(8*side 25)*side i^6 by ring,side_card]
  rw [one_mul, div_eq_inv_mul]
  gcongr; norm_num [side]

lemma image_income (s : Scene M) (d : Finset (Grid M)) (b : Bool)
    (i m : ℕ) (f : Dome (precision i m) d → ℝ) :
    ∑ x, portrait b s d i m x * f x =
      rung s (channel (optic s b)) (fun x y => f (y,tiles (precision i m) d x)) := by
  unfold portrait; rw [rung_hist]
  unfold rung addMass
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [mul_assoc,← Finset.mul_sum]
  congr 1
  exact Ex_send _ _ _

lemma portrait_compare (s : Scene M) (b : Bool) (d : Finset (Grid M))
    (i m : ℕ) (c : Grid M → ℂ) (p : Grid M)
    (F : TileN (precision i m) d → ℂ) (h : ∀ x, ‖chi p x-F (tiles (precision i m) d x)‖ ≤ sharp i)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hp : s.here.ok M)
    (ha : 0 ≤ s.wage) (hv : 0 ≤ s.norm) (hs : share s ≤ 4) :
    |sales b s c p - ∑ x, portrait b s d i m x * utility b (c x.1) (F x.2)| ≤
      8*sharp i := by
  rw [image_income _ _ _ _ _ (fun x => utility b (c x.1) (F x.2))]
  unfold sales
  apply le_trans _ (show share s*(2*sharp i) ≤ 8*sharp i from by nlinarith [sharp_pos i])
  apply rung_error s ha hv hp
  intro j k
  exact (utility_diff _ _ _ _ (hc k)).trans (mul_le_mul_of_nonneg_left (h j) (by norm_num))

/-- Scenes with close portrait. No equality of scene or area needed. -/
lemma close_display (s t : Scene M) (b : Bool) (d : Finset (Grid M)) (i m : ℕ) (hd : d.card ≤ rangeIx m)
    (p : Grid M) (he : enclosed d 1 p) (hh : distance (portrait b s d i m) (portrait b t d i m) ≤ sharp i)
    (hs : ReadyAt s) (ht : ReadyAt t) (ha : 0 ≤ s.norm) (hb : 0 ≤ t.norm)
    (hc : share s ≤ 4) (hC : share t ≤ 4) :
    magnitude b s p ≤ magnitude b t p +20*sharp i := by
  classical
  obtain ⟨f,hf,hF⟩ := painted _ _ he (precision i m)
  have hx (x) := (hF x).trans (coordinate_le _ _ hd)
  obtain ⟨g,hg,hG⟩ := (test_complete b _ hs.2 ha p).2
  let Q (x : Dome (precision i m) d) := utility b (g x.1) (f x.2)
  let P (s : Scene M) := portrait b s d i m
  let V (s : Scene M) := ∑ x, P s x*Q x
  have hV : V s ≤ V t +3*sharp i := by
    rw [add_comm]; apply sub_le_iff_le_add.mp
    unfold V; rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x, 3* |P s x-P t x| := Finset.sum_le_sum fun x _ => by
        rw [← sub_mul]
        apply le_trans (le_abs_self _)
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (utility_bounds _ _ _ (hg _) (hf _)) (abs_nonneg _)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have h1 : |sales b s g p - V s| ≤ 8*sharp i :=
    portrait_compare _ _ _ _ _ _ _ _ hx hg hs.1 hs.2 ha hc
  have h2 : |sales b t g p - V t| ≤ 8*sharp i :=
    portrait_compare _ _ _ _ _ _ _ _ hx hg ht.1 ht.2 hb hC
  have hi := (test_complete b t ht.2 hb p).1 _ hg
  rw [hG] at h1
  linarith [sharp_pos i,(abs_le.mp h1).2,(abs_le.mp h2).1]

end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI

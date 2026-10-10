import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Hashing
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.LossCounts

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointCoarseHashing

attribute [local instance] Classical.propDecidable

abbrev Word (P : Type*) := P → Fin 17
abbrev Triple (P : Type*) := Word P × Word P × Word P

variable {P : Type*}

def HasSupportSum (S : P → ℕ) (e : Triple P) : Prop :=
  ∀ p, (e.1 p).val + (e.2.1 p).val + (e.2.2 p).val = S p

theorem eq_of_shared_xy (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hy : e.2.1 = f.2.1) : e = f := by
  have hz : e.2.2 = f.2.2 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hy] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_shared_xz (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hz : e.2.2 = f.2.2) : e = f := by
  have hy : e.2.1 = f.2.1 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hz] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_shared_yz (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hy : e.2.1 = f.2.1) (hz : e.2.2 = f.2.2) : e = f := by
  have hx : e.1 = f.1 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hy, hz] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

def castWord (k : ℕ) (w : Word P) : P → ZMod (37 ^ k) :=
  fun p => (w p).val

def twoUnit (k : ℕ) : (ZMod (37 ^ k))ˣ :=
  (JointHashing.small_nat_isUnit k 2 (by decide) (by decide)).unit

theorem twoUnit_coe (k : ℕ) : (twoUnit k : ZMod (37 ^ k)) = 2 := by
  exact (JointHashing.small_nat_isUnit k 2 (by decide) (by decide)).unit_spec

theorem supportSum_cast (k : ℕ) (S : P → ℕ) (e : Triple P)
    (he : HasSupportSum S e) :
    castWord k e.1 + castWord k e.2.1 + castWord k e.2.2 =
      fun p => (S p : ZMod (37 ^ k)) := by
  funext p
  have h := congrArg (fun n : ℕ => (n : ZMod (37 ^ k))) (he p)
  simpa only [Nat.cast_add, Pi.add_apply, castWord] using h

theorem shared_z_cast_sum (k : ℕ) (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hz : f.2.2 = e.2.2) :
    castWord k f.1 + castWord k f.2.1 = castWord k e.1 + castWord k e.2.1 := by
  have h := (supportSum_cast k S f hf).trans (supportSum_cast k S e he).symm
  rw [hz] at h
  exact add_right_cancel h

section FiniteHashing

variable [Fintype P]

abbrev Sample (P : Type*) (k : ℕ) := JointHashing.Sample P (ZMod (37 ^ k))

def Survives (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) (s : Sample P k) : Prop :=
  JointHashing.Survives (U : Set (ZMod (37 ^ k))) (castWord k e.1) (castWord k e.2.1) s

theorem full_survival_iff (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (s : Sample P k) :
    (JointHashing.xHash s (castWord k e.1) ∈ U ∧
      JointHashing.yHash s (castWord k e.2.1) ∈ U ∧
      JointHashing.zHash (twoUnit k) s (fun p => (S p : ZMod (37 ^ k)))
        (castWord k e.2.2) ∈ U) ↔ Survives k U e s := by
  exact JointHashing.full_survival_iff (twoUnit k) (twoUnit_coe k)
    (U : Set (ZMod (37 ^ k))) hAP s (castWord k e.1) (castWord k e.2.1)
    (castWord k e.2.2) (fun p => (S p : ZMod (37 ^ k))) (supportSum_cast k S e he)

theorem survival_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    Fintype.card {s : Sample P k // Survives k U e s} =
      (37 ^ k) ^ Fintype.card P * U.card := by
  have h := JointHashing.survival_card U (castWord k e.1) (castWord k e.2.1)
  simp only [Survives, ZMod.card] at h ⊢
  refine Eq.trans ?_ h
  exact Fintype.card_congr (Equiv.refl _)

theorem shared_x_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hx : f.1 = e.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hy : f.2.1 ≠ e.2.1 := fun hy => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.2.1 e.2.1 hy
  have h := JointHashing.shared_x_collision_card_mul U (castWord k e.1)
    (castWord k e.2.1) (castWord k f.2.1) i hi.unit hi.unit_spec.symm
  simp only [Survives, hx, ZMod.card] at h ⊢
  refine Eq.trans ?_ (Eq.trans h ?_)
  · exact congrArg (fun n : ℕ => 37 ^ k * n) (Fintype.card_congr (Equiv.refl _))
  · exact Fintype.card_congr (Equiv.refl _)

theorem shared_y_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hy : f.2.1 = e.2.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_y_collision_card_mul U (castWord k e.1)
    (castWord k f.1) (castWord k e.2.1) i hi.unit hi.unit_spec.symm
  simp only [Survives, hy, ZMod.card] at h ⊢
  refine Eq.trans ?_ (Eq.trans h ?_)
  · exact congrArg (fun n : ℕ => 37 ^ k * n) (Fintype.card_congr (Equiv.refl _))
  · exact Fintype.card_congr (Equiv.refl _)

theorem shared_z_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hz : f.2.2 = e.2.2) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xz S f e hf he hx hz)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_z_collision_card_mul (twoUnit k) (twoUnit_coe k)
    U (castWord k e.1) (castWord k f.1) (castWord k e.2.1) (castWord k f.2.1)
    (shared_z_cast_sum k S e f he hf hz) i hi.unit hi.unit_spec.symm
  simp only [Survives, ZMod.card] at h ⊢
  refine Eq.trans ?_ (Eq.trans h ?_)
  · exact congrArg (fun n : ℕ => 37 ^ k * n) (Fintype.card_congr (Equiv.refl _))
  · exact Fintype.card_congr (Equiv.refl _)

def SharesSide (e f : Triple P) : Prop :=
  f.1 = e.1 ∨ f.2.1 = e.2.1 ∨ f.2.2 = e.2.2

theorem pair_survival_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  rcases hshare with hx | hy | hz
  · exact shared_x_card_mul k U S e f he hf hne hx
  · exact shared_y_card_mul k U S e f he hf hne hy
  · exact shared_z_card_mul k U S e f he hf hne hz

def ownEvent (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) : Finset (Sample P k) :=
  Finset.univ.filter (Survives k U e)

theorem ownEvent_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    (ownEvent k U e).card = (37 ^ k) ^ Fintype.card P * U.card := by
  simpa only [ownEvent, Fintype.card_subtype] using survival_card k U e

theorem pair_event_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter (Survives k U f)).card = (ownEvent k U e).card := by
  simpa only [ownEvent, Finset.filter_filter, Fintype.card_subtype] using
    pair_survival_card_mul k U S e f he hf hne hshare

theorem competitor_union_card_mul_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter
      (fun s => ∃ f ∈ competitors, Survives k U f s)).card ≤
        competitors.card * (ownEvent k U e).card := by
  apply JointLossCounts.competitor_union_card_mul_le
  intro f hf'
  exact (pair_event_card_mul k U S e f he (hf f hf') (hne f hf') (hshare f hf')).le

theorem competitor_union_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      ((competitors.card : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U e).card : ℝ) := by
  have hM : (0 : ℝ) < ((37 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by decide : 0 < (37 : ℕ)) k)
  have h := competitor_union_card_mul_le k U S e he competitors hf hne hshare
  have hR : ((37 ^ k : ℕ) : ℝ) *
      (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      (competitors.card : ℝ) * ((ownEvent k U e).card : ℝ) := by exact_mod_cast h
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hM).2 (by simpa only [mul_comm] using hR)

theorem pair_survival_fraction (k : ℕ) (U : Finset (ZMod (37 ^ k))) (hU : U.Nonempty)
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (((ownEvent k U e).filter (Survives k U f)).card : ℝ) / ((ownEvent k U e).card : ℝ) =
      1 / ((37 ^ k : ℕ) : ℝ) := by
  have hM : (0 : ℕ) < 37 ^ k := pow_pos (by decide) k
  have hS : 0 < (ownEvent k U e).card := by
    rw [ownEvent_card]
    exact Nat.mul_pos (pow_pos hM _) (Finset.card_pos.mpr hU)
  apply (div_eq_div_iff (by exact_mod_cast Nat.ne_of_gt hS)
    (by exact_mod_cast Nat.ne_of_gt hM)).2
  have h := congrArg (fun n : ℕ => (n : ℝ)) (pair_event_card_mul k U S e f he hf hne hshare)
  simpa only [Nat.cast_mul, one_mul, mul_comm] using h

end FiniteHashing

end MatrixMultiplication.JointCoarseHashing

end

end OAI

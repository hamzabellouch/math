import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336AdditiveD139

private theorem limsup_le_limsup_add_of_unit_bounds
    {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ n, b n ∈ Set.Icc (0 : ℝ) 1)
    (hab : ∀ n, a n ≤ b n + C) :
    limsup a atTop ≤ limsup b atTop + C := by
  have haCob : IsCoboundedUnder (· ≤ ·) atTop a :=
    isCoboundedUnder_le_of_le atTop (fun n => (ha n).1)
  have hbBound : IsBoundedUnder (· ≤ ·) atTop b :=
    isBoundedUnder_of ⟨1, fun n => (hb n).2⟩
  have hbCob : IsCoboundedUnder (· ≤ ·) atTop b :=
    isCoboundedUnder_le_of_le atTop (fun n => (hb n).1)
  have hshift : IsBoundedUnder (· ≤ ·) atTop (fun n => b n + C) :=
    isBoundedUnder_of ⟨1 + C, fun n => by linarith [(hb n).2]⟩
  have h := limsup_le_limsup (Eventually.of_forall hab) haCob hshift
  rwa [limsup_add_const atTop b C hbBound hbCob] at h

theorem abs_limsup_sub_limsup_le_of_unit_bounds
    {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ n, b n ∈ Set.Icc (0 : ℝ) 1)
    (hab : ∀ n, |a n - b n| ≤ C) :
    |limsup a atTop - limsup b atTop| ≤ C := by
  have hab' : limsup a atTop ≤ limsup b atTop + C :=
    limsup_le_limsup_add_of_unit_bounds ha hb (fun n => by
      have h := (abs_le.mp (hab n)).2
      linarith)
  have hba' : limsup b atTop ≤ limsup a atTop + C :=
    limsup_le_limsup_add_of_unit_bounds hb ha (fun n => by
      have h := (abs_le.mp (hab n)).1
      linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def limsupDrift {Ω : Type u_1} {I : Type u_2} (b : ℕ → Ω → I → ℝ) (w : Ω) (i : I) : ℝ :=
  limsup (fun n => b n w i) atTop

theorem limsupDrift_mem_unitInterval {Ω : Type u_3} {I : Type u_4}
    {b : ℕ → Ω → I → ℝ}
    (hb : ∀ n w i, b n w i ∈ Set.Icc (0 : ℝ) 1) (w : Ω) (i : I) :
    limsupDrift b w i ∈ Set.Icc (0 : ℝ) 1 := by
  have hBound : IsBoundedUnder (· ≤ ·) atTop (fun n => b n w i) :=
    isBoundedUnder_of ⟨1, fun n => (hb n w i).2⟩
  have hCob : IsCoboundedUnder (· ≤ ·) atTop (fun n => b n w i) :=
    isCoboundedUnder_le_of_le atTop (fun n => (hb n w i).1)
  constructor
  · apply le_limsup_of_le hBound
    intro c hc
    obtain ⟨n, hn⟩ := hc.exists
    exact (hb n w i).1.trans hn
  · exact limsup_le_of_le hCob (Eventually.of_forall (fun n => (hb n w i).2))

theorem measurable_limsupDrift {Ω : Type u_5} {I : Type u_6} [MeasurableSpace Ω]
    {b : ℕ → Ω → I → ℝ} (hb : ∀ n, Measurable (b n)) :
    Measurable (limsupDrift b) := by
  apply Measurable.of_eval
  intro i
  exact Measurable.limsup (fun n => (measurable_pi_apply i).comp (hb n))

theorem limsupDrift_abs_sub_le {Ω : Type u_7} {I : Type u_8} {b : ℕ → Ω → I → ℝ}
    (hb : ∀ n w i, b n w i ∈ Set.Icc (0 : ℝ) 1)
    {w w' : Ω} {C : ℝ} (h : ∀ n i, |b n w i - b n w' i| ≤ C) (i : I) :
    |limsupDrift b w i - limsupDrift b w' i| ≤ C :=
  abs_limsup_sub_limsup_le_of_unit_bounds
    (fun n => hb n w i) (fun n => hb n w' i) (fun n => h n i)

theorem limsupDrift_reindex {Ω : Type u_9} {I : Type u_10} {b : ℕ → Ω → I → ℝ}
    (A : Ω → Ω) (e : I → I)
    (hb : ∀ n w i, b n (A w) i = b n w (e i)) (w : Ω) (i : I) :
    limsupDrift b (A w) i = limsupDrift b w (e i) := by
  unfold limsupDrift
  congr 1
  funext n
  exact hb n w i

theorem limsupDrift_leftTranslate {Γ : Type u_11} [Group Γ]
    {b : ℕ → (Γ → ℝ) → Γ → ℝ}
    (hb : ∀ n (g : Γ) y, b n (leftTranslate g y) = leftTranslate g (b n y))
    (g : Γ) (y : Γ → ℝ) :
    limsupDrift b (leftTranslate g y) = leftTranslate g (limsupDrift b y) := by
  funext i
  exact limsupDrift_reindex (leftTranslate g) (fun i => g⁻¹ * i)
    (fun n w i => congrFun (hb n g w) i) y i

end Problem336AdditiveD139

end

end OAI

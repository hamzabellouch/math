import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Routing
import OAI.MathematicalPhysics.SheetFlows.RationalFormula

namespace OAI

/-! SheetFlows formula profiles. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

def RationalParameter (x : ℝ) : Prop := ∃ q : ℚ, (q:ℝ) = x

namespace RationalParameter

theorem rat (q : ℚ) : RationalParameter (q:ℝ) := ⟨q,rfl⟩
theorem ofNat (n : ℕ) : RationalParameter (n:ℝ) := ⟨n,by simp⟩
theorem add {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b,by simp⟩
theorem sub {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a-b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a-b,by simp⟩
theorem mul {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a*b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a*b,by simp⟩
theorem div {a b : ℝ} (ha : RationalParameter a) (hb : RationalParameter b) :
    RationalParameter (a/b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a/b,by simp⟩
theorem neg {a : ℝ} (ha : RationalParameter a) : RationalParameter (-a) := by
  obtain ⟨a,rfl⟩ := ha
  exact ⟨-a,by simp⟩
end RationalParameter

theorem Rectangle.center_rational (R : Rectangle) (j : Fin 2) :
    RationalParameter (R.center j) :=
  ((RationalParameter.rat _).add (.rat _)).div (.ofNat 2)

theorem Rectangle.halfWidth_rational (R : Rectangle) (j : Fin 2) :
    RationalParameter (R.halfWidth j) :=
  ((RationalParameter.rat _).sub (.rat _)).div (.ofNat 2)

def PeriodicJet.sub {T : ℚ} {f g : ℝ → ℝ} (p : PeriodicJet T f) (q : PeriodicJet T g) :
    PeriodicJet T (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg,neg_one_mul,Rat.cast_neg,Rat.cast_one] using
    p.add ((PeriodicJet.const T p.positive (-1)).mul q)

theorem Cprofile_hasJet {h d c : ℝ}
    (hh : RationalParameter h) (hd : RationalParameter d) (hc : RationalParameter c)
    (hpos : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    Nonempty (PeriodicJet 10 (Cprofile h d c)) := by
  obtain ⟨h,rfl⟩ := hh; obtain ⟨d,rfl⟩ := hd; obtain ⟨c,rfl⟩ := hc
  exact ⟨Cprofile_jet h d c (by exact_mod_cast hpos) (by exact_mod_cast hl) (by exact_mod_cast hu)⟩

theorem Dprofile_hasJet {h d c : ℝ}
    (hh : RationalParameter h) (hd : RationalParameter d) (hc : RationalParameter c)
    (hpos : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    Nonempty (PeriodicJet 10 (Dprofile h d c)) := by
  obtain ⟨h,rfl⟩ := hh; obtain ⟨d,rfl⟩ := hd; obtain ⟨c,rfl⟩ := hc
  exact ⟨Dprofile_jet h d c (by exact_mod_cast hpos) (by exact_mod_cast hl) (by exact_mod_cast hu)⟩

namespace StationaryPulse

def RationalFormula (p : StationaryPulse) : Prop := HasRationalFormula (fun _ => p.field)

theorem RationalFormula.scale {p : StationaryPulse} {c : ℝ}
    (hp : p.RationalFormula) (hc : RationalParameter c) : (p.scale c).RationalFormula := by
  obtain ⟨q,rfl⟩ := hc
  exact hp.smul q

theorem rationalFormula_tensor (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j, Function.Periodic (g j) 10)
    (hi : ∀ s, g i s = 1) (j : Fin 3)
    (hz : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0)
    (hr : ∀ j, Nonempty (PeriodicJet 10 (g j))) :
    (tensor i g hsm hp hi j hz).RationalFormula := tensorVelocity_formula i g hr

end StationaryPulse

variable (d : Collar) (hd : RationalParameter d.size)
include hd

theorem verticalPulse_formula (R : Rectangle) (hR : R.inCodingSquare) {s : ℝ}
    (hs : s ∈ Set.Icc 0 4) (hsr : RationalParameter s) :
    (verticalPulse d R hR s).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  have h (j : Fin 2) (v : ℝ) (hvr : RationalParameter v) (hv : v ∈ Set.Icc 0 4) :
      Nonempty (PeriodicJet 10 (Cprofile (R.halfWidth j) d.size (R.center j+v))) :=
    Cprofile_hasJet (R.halfWidth_rational j) hd ((R.center_rational j).add hvr)
      d.positive (rect_support_chart d R hR j hv).1 (rect_support_chart d R hR j hv).2
  intro j
  fin_cases j
  · exact h 0 s hsr hs
  · obtain ⟨a⟩ := h 1 0 (by exact ⟨0, by norm_num⟩) (by norm_num)
    obtain ⟨b⟩ := h 1 4 (by exact ⟨4, by norm_num⟩) (by norm_num)
    exact ⟨by simpa using a.sub b⟩
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩

theorem horizontalPulse_formula (j : Fin 2) : (horizontalPulse d j).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · obtain ⟨a⟩ := Cprofile_hasJet (show RationalParameter 0 from ⟨0, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩) d.positive
      (show 0+d.size ≤ 5 by linarith [d.small])
      (show 5+(0+d.size) ≤ 10 by linarith [d.small])
    obtain ⟨b⟩ := Cprofile_hasJet (show RationalParameter 0 from ⟨0, by norm_num⟩) hd (show RationalParameter 8 from ⟨8, by norm_num⟩) d.positive
      (show 0+d.size ≤ 8 by linarith [d.small])
      (show 8+(0+d.size) ≤ 10 by linarith [d.small])
    exact ⟨a.sub b⟩

theorem coreLift0_formula : (coreLift0 d).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact Dprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact Cprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 6 from ⟨6, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩

theorem coreLift1_formula : (coreLift1 d).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact Cprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact Dprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 6 from ⟨6, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩

theorem coreHorizontal_formula (j : Fin 2) : (coreHorizontal d j).RationalFormula := by
  apply StationaryPulse.rationalFormula_tensor
  intro k
  fin_cases k
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · exact ⟨by simpa using PeriodicJet.const 10 (by norm_num) 1⟩
  · exact Dprofile_hasJet (show RationalParameter (1/2) from ⟨1/2, by norm_num⟩) hd (show RationalParameter 5 from ⟨5, by norm_num⟩)
      d.positive (by linarith [d.small]) (by linarith [d.small])

theorem travelProgram_formula (v : Plane) (hv : ∀ j, RationalParameter (v j)) :
    ∀ p ∈ travelProgram d v, p.RationalFormula := by
  intro p hp
  simp only [travelProgram,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact (horizontalPulse_formula d hd 0).scale (hv 0)
  · exact (horizontalPulse_formula d hd 1).scale (hv 1)

theorem tripleProgram0_formula {l : ℝ} (hl : RationalParameter l) :
    ∀ p ∈ tripleProgram0 d l, p.RationalFormula := by
  have h1 : RationalParameter (1:ℝ) := ⟨1,by norm_num⟩
  intro p hp
  simp only [tripleProgram0,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact coreLift0_formula d hd
  · exact (coreHorizontal_formula d hd 0).scale (hl.sub h1)
  · exact (coreLift0_formula d hd).scale (h1.neg.div hl)

theorem tripleProgram1_formula {l : ℝ} (hl : RationalParameter l) :
    ∀ p ∈ tripleProgram1 d l, p.RationalFormula := by
  have h1 : RationalParameter (1:ℝ) := ⟨1,by norm_num⟩
  intro p hp
  simp only [tripleProgram1,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact coreLift1_formula d hd
  · exact (coreHorizontal_formula d hd 1).scale (hl.sub h1)
  · exact (coreLift1_formula d hd).scale (h1.neg.div hl)

theorem processingProgram_formula {l m : ℝ} (hl : RationalParameter l)
    (hm : RationalParameter m) : ∀ p ∈ processingProgram d l m, p.RationalFormula := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact tripleProgram0_formula d hd hl p hp
  · exact tripleProgram1_formula d hd hm p hp

theorem evacuateProgram_formula (R : Rectangle) (hR : R.inCodingSquare) :
    ∀ p ∈ evacuateProgram d R hR, p.RationalFormula := by
  intro p hp
  simp only [evacuateProgram,List.mem_append,List.mem_singleton] at hp
  rcases hp with (rfl | hp) | rfl
  · exact (verticalPulse_formula d hd R hR (by norm_num) ⟨0,by norm_num⟩).scale ⟨3,by norm_num⟩
  · apply travelProgram_formula d hd _ _ _ hp
    intro j; fin_cases j
    · exact ⟨4,by norm_num⟩
    · exact ⟨0,by norm_num⟩
  · exact (verticalPulse_formula d hd R hR (by norm_num) ⟨4,by norm_num⟩).scale ⟨-3,by norm_num⟩

theorem instructionProgram_formula {N : ℕ} (D : SheetData N) (i : Fin N) :
    ∀ p ∈ instructionProgram d D i, p.RationalFormula := by
  intro p hp
  simp only [instructionProgram,List.mem_append,List.mem_singleton] at hp
  rcases hp with (((rfl | hp) | hp) | hp) | rfl
  · exact (verticalPulse_formula d hd _ (D.source_inside i) (by norm_num)
      ⟨4,by norm_num⟩).scale ⟨3,by norm_num⟩
  · apply travelProgram_formula d hd _ _ _ hp
    intro j; fin_cases j
    · exact (show RationalParameter 1 from ⟨1,by norm_num⟩).sub ((D.source i).center_rational 0)
    · exact (show RationalParameter 6 from ⟨6,by norm_num⟩).sub ((D.source i).center_rational 1)
  · exact processingProgram_formula d hd (.rat _) (.rat _) _ hp
  · apply travelProgram_formula d hd _ _ _ hp
    intro j; fin_cases j
    · exact ((D.target i).center_rational 0).sub ⟨5,by norm_num⟩
    · exact ((D.target i).center_rational 1).sub ⟨6,by norm_num⟩
  · exact (verticalPulse_formula d hd _ (D.target_inside i) (by norm_num)
      ⟨0,by norm_num⟩).scale ⟨-3,by norm_num⟩

theorem sheetProgram_formula {N : ℕ} (D : SheetData N) :
    ∀ p ∈ sheetProgram d D, p.RationalFormula := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
    exact evacuateProgram_formula d hd _ (D.source_inside i) p hi
  · obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
    exact instructionProgram_formula d hd D i p hi

theorem sheetVelocity_formula {N : ℕ} (D : SheetData N) :
    HasRationalFormula (scheduleVelocity
      (fun i : Fin (sheetProgram d D).length => ((sheetProgram d D).get i).field)) :=
  scheduleVelocity_formula _ (fun index => sheetProgram_formula d hd D _ (List.get_mem _ index))

end Solenoidal
end

end OAI

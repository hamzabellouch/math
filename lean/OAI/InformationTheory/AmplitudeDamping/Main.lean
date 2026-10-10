import OAI.InformationTheory.AmplitudeDamping.CapacityAchievability

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

theorem capacity_formula (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : Maximizes γ ν p) :
    capacity γ ν=objective γ ν p/Real.log 2 := by
  have hzero := zero_achievable γ ν hγ hν
  have hbdd : BddAbove {R : ℝ | Achievable γ ν R} :=
    ⟨objective γ ν p/Real.log 2,fun _ hR ↦ achievable_upper γ ν hγ hν hp hR⟩
  have hnonempty : {R : ℝ | Achievable γ ν R}.Nonempty := ⟨0,hzero⟩
  have hcap0 : 0 ≤ capacity γ ν := le_csSup hbdd hzero
  apply le_antisymm
  · exact csSup_le hnonempty (fun _ hR ↦ achievable_upper γ ν hγ hν hp hR)
  · by_contra! hbad
    let R := (capacity γ ν+objective γ ν p/Real.log 2)/2
    have hRcap : capacity γ ν < R := by dsimp [R]; linarith
    have hRχ : R < objective γ ν p/Real.log 2 := by dsimp [R]; linarith
    have hR0 : 0 ≤ R := hcap0.trans hRcap.le
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hrχ : R*Real.log 2 < objective γ ν p := (lt_div_iff₀ hl).mp hRχ
    have ha := phase_rate_achievable γ ν hγ hν hp.1 (mul_nonneg hR0 hl.le) hrχ
    rw [mul_div_cancel_right₀ R hl.ne'] at ha
    exact (not_le_of_gt hRcap) (le_csSup hbdd ha)

theorem capacity_holevo (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) : capacity γ ν=holevo γ ν 1 := by
  obtain ⟨p,hp,hmax⟩ := exists_maximizer γ ν
  rw [capacity_formula γ ν hγ hν ⟨hp,hmax⟩,holevo_formula γ ν hγ hν ⟨hp,hmax⟩ 1]
  norm_num
  ring

theorem main (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hν : ν ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) * holevo γ ν 1) ∧
    (∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n : ℝ) / Real.log 2 * objective γ ν p) ∧
    capacity γ ν = holevo γ ν 1 ∧
    (∀ p : ℝ, Maximizes γ ν p → ∀ n : ℕ, 1 ≤ n →
      (∀ s : Basis n, IsState (phaseState p s)) ∧
      holevo γ ν n = phaseValue γ ν p n) := by
  exact ⟨fun n _ ↦ holevo_additive γ ν hγ hν n,
    holevo_maximizer γ ν hγ hν,capacity_holevo γ ν hγ hν,
    fun p hp n _ ↦ phase_attainment γ ν hγ hν hp n⟩

end GAD

end

end OAI

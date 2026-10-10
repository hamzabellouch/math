import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingWindow

namespace OAI

/-!
# Uniform terminal shearing windows

The stopping-time estimate gives convergence uniformly throughout a
terminal window whose relative length shrinks to zero. In particular,
the error relative to the limiting shear lies in every identity
neighborhood throughout that window.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma eventually_uniform_of_all_selections
    {A B : Type*} [TopologicalSpace B]
    (S : ℕ → Set A) (hS : ∀ n, (S n).Nonempty)
    (F : ℕ → A → B) (b : B)
    (hlim : ∀ s : ℕ → A, (∀ n, s n ∈ S n) →
      Tendsto (fun n => F n (s n)) atTop (𝓝 b)) :
    ∀ U ∈ 𝓝 b, ∀ᶠ n in atTop, ∀ x ∈ S n, F n x ∈ U := by
  classical
  intro U hU
  let s (n : ℕ) : A :=
    if h : ∃ x ∈ S n, F n x ∉ U then h.choose else (hS n).choose
  have hs (n : ℕ) : s n ∈ S n := by
    dsimp only [s]
    split_ifs with h
    · exact h.choose_spec.1
    · exact (hS n).choose_spec
  have ht := (hlim s hs).eventually hU
  filter_upwards [ht] with n hn x hx
  by_contra hbad
  have hb : ∃ y ∈ S n, F n y ∉ U := ⟨x, hx, hbad⟩
  have hsbad : F n (s n) ∉ U := by
    simpa only [s, dite_eq_left hb] using hb.choose_spec.2
  exact hsbad hn

theorem root_conjugation_terminal_uniform
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (T δ : ℕ → ℝ) (a : ℝ)
    (hT : ∀ m, 0 < T m)
    (hbound : ∀ m, ∀ t ∈ Icc 0 (T m), rootShearSize hij (g m) t ≤ a)
    (hδ : ∀ m, δ m ∈ Icc (0 : ℝ) 1)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-T m)) atTop (𝓝 h)) :
    ∀ U ∈ 𝓝 h, ∀ᶠ m in atTop, ∀ s ∈ Icc (1 - δ m) 1,
      Matrix.SpecialLinearGroup.transvection hij (s * T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(s * T m)) ∈ U := by
  apply eventually_uniform_of_all_selections
    (fun m => Icc (1 - δ m) 1)
    (fun m => ⟨1, by constructor <;> linarith [(hδ m).1]⟩)
  intro s hs
  have hsunit (m : ℕ) : s m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [(hs m).1, (hδ m).2]
    · exact (hs m).2
  have hslow : Tendsto (fun m => 1 - δ m) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hδlim
  have hslim : Tendsto s atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hslow tendsto_const_nhds
      (fun m => (hs m).1) (fun m => (hs m).2)
  exact root_conjugation_window_tendsto hij g T s a hT hbound hsunit hslim h hlim

/-- The small multiplying error in the pair-measure argument is
uniformly close to identity over the entire window. -/
theorem root_conjugation_terminal_error
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (T δ : ℕ → ℝ) (a : ℝ)
    (hT : ∀ m, 0 < T m)
    (hbound : ∀ m, ∀ t ∈ Icc 0 (T m), rootShearSize hij (g m) t ≤ a)
    (hδ : ∀ m, δ m ∈ Icc (0 : ℝ) 1)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-T m)) atTop (𝓝 h)) :
    ∀ U ∈ 𝓝 (1 : G n), ∀ᶠ m in atTop, ∀ s ∈ Icc (1 - δ m) 1,
      (Matrix.SpecialLinearGroup.transvection hij (s * T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(s * T m))) * h⁻¹ ∈ U := by
  intro U hU
  have hp : {z : G n | z * h⁻¹ ∈ U} ∈ 𝓝 h := by
    apply (continuous_mul_const h⁻¹).tendsto h
    simpa only [mul_inv_cancel] using hU
  exact root_conjugation_terminal_uniform hij g T δ a hT hbound hδ hδlim h hlim _ hp

end DukePrimeDegree

end

end OAI

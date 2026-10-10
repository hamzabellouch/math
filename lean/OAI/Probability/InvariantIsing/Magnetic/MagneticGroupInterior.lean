import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupParameterBound

namespace OAI

/-! An interior limit gives a common strict magnetization bound for all
sufficiently large members of a finite family. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma exists_uniform_magnetization_radius {A : Type*} [Fintype A]
    (s : ℕ → A → ℝ) (t : A → ℝ) (hs : Tendsto s atTop (𝓝 t))
    (ht : ∀ a, |t a|<1) :
    ∃ r : ℝ, r<1 ∧ (∀ a, |t a|≤r) ∧ ∀ᶠ k in atTop, ∀ a, |s k a|≤r := by
  classical
  by_cases hA : Nonempty A
  · have : Nonempty A := hA
    have hne : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    let M := Finset.univ.sup' hne (fun a => |t a|)
    have hM : M<1 := (Finset.sup'_lt_iff hne).mpr (fun a _ => ht a)
    obtain ⟨r, hMr, hr⟩ := exists_between hM
    have htr a : |t a|<r := (Finset.le_sup' (fun a => |t a|) (Finset.mem_univ a)).trans_lt hMr
    refine ⟨r, hr, fun a => (htr a).le, ?_⟩
    rw [Filter.eventually_all]
    intro a
    exact ((((tendsto_pi_nhds.mp hs) a).abs).eventually (Iio_mem_nhds (htr a))).mono
      (fun _ h => h.le)
  · have : IsEmpty A := not_nonempty_iff.mp hA
    exact ⟨0, by norm_num, fun a => isEmptyElim a, Filter.Eventually.of_forall (fun _ a => isEmptyElim a)⟩

end InvariantIsing

end

end OAI

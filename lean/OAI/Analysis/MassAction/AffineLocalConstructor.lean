import OAI.Analysis.MassAction.AffineLayers
import OAI.Analysis.MassAction.AffineCertificates

namespace OAI

open Filter Topology

noncomputable section
namespace Problem326.Affine

/-- Turn the output of the finite layer construction into the canonical local
certificate. The finite family admits one common stronger decay exponent. -/
theorem localCertificate_of_layers {d : ℕ} (hd : 0 < d)
    {a t b : ℝ} (htb : t < b) (E : (Fin d → ℝ) → ℝ)
    (hE₀ : 0 < E (fun _ => t))
    (hmake : ∀ k : ℕ, 0 < k → k < d → ∀ β : ℝ, t < β → β < b →
      ∃ F : Finset (Label d), LayerCertificate t b E k β F) :
    Nonempty (LocalCertificate d a b t E) := by
  classical
  obtain ⟨Λ, hbase, happrox, hdata⟩ :=
    exists_fixed_minimum_family_of_layers (a := a) hd htb E hE₀ hmake
  have hdecay : ∀ L : Λ, ∃ q : ℝ, t < q ∧
      Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) L.val.offset (fun h : ℝ => h ^ q) := by
    intro L
    exact (hdata L.val L.property).2.2
  choose q hqt hqdec using hdecay
  obtain ⟨η, htη, hηupper, hηq⟩ := exists_threshold (Finset.univ : Finset Λ)
    (fun L => q L - t) (fun L _ => sub_pos.mpr (hqt L))
    (show t < t + 1 by linarith)
  refine ⟨{
    labels := Λ
    baseline := hbase
    slopes := fun L hL => (hdata L hL).1
    minima := fun L hL => (hdata L hL).2.1
    decayExponent := η
    decay_gt := htη
    offsets := ?_
    approximation := happrox
  }⟩
  intro L hL
  let J : Λ := ⟨L, hL⟩
  have hηqJ : η < q J := by
    have hbound := hηq J (Finset.mem_univ J)
    linarith
  exact offset_isLittleO_of_normalized_limit hηqJ (hqdec J).tendsto_div_nhds_zero

end Problem326.Affine

end

end OAI

import OAI.Analysis.MassAction.TypeFamily
import OAI.Analysis.MassAction.AffineCertificates
import OAI.Analysis.MassAction.AffineLayers

namespace OAI

noncomputable section
open Filter Topology

namespace Problem326.Affine

local instance {d : ℕ} : DecidableEq (Label d) := Classical.decEq _

/-- Project the full lower-dimensional approximation certificate into a member of the
injection-indexed type family. The approximating exponents need not stay in any cube. -/
theorem typeFamily_approximatesOnSupport {k d : ℕ} (t β b : ℝ)
    (E : (Fin d → ℝ) → ℝ)
    (C : ∀ e : Fin k ↪ Fin d,
      FullCertificate k β b (fun s => E (embedCoordinates e t s)))
    (e : Fin k ↪ Fin d) {L : Label k} (hL : L ∈ (C e).labels) :
    ApproximatesOnSupport
      (typeFamily t β (fun e => (C e).labels)) (L.embed e t β)
      (Finset.univ.map e) t b β E := by
  intro h p p₀ hh hh0 hp hp₀ hraised ha
  have hpProj : Cube β b (fun j => p₀ (e j)) := by
    intro j
    exact ⟨hraised (e j) (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩), (hp₀ (e j)).2⟩
  have hlocal : ∀ n, Active (C e).labels L (h n)
      (powerPoint (h n) (fun j => p n (e j))) := by
    intro n
    exact typeFamily_active_project t β (h n) (fun e => (C e).labels) e hL (p n) (ha n)
  have herr := (C e).approximation L hL h (fun n j => p n (e j))
    (fun j => p₀ (e j)) hh hh0 (tendsto_project_coordinates e hp) hpProj hlocal
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
  exact embedded_error_on_range e t herr (e j) ⟨j, rfl⟩

/-- The actual positive-type constructor: lower-dimensional full certificates for every
coordinate injection produce the exact layer certificate consumed by fixed-minimum assembly. -/
theorem typeFamily_layerCertificate {k d : ℕ} (hk : 0 < k)
    {t β b : ℝ} (htβ : t < β) (hβb : β < b)
    (E : (Fin d → ℝ) → ℝ)
    (hE : ∀ r, Cube t b r → 0 < E r)
    (C : ∀ e : Fin k ↪ Fin d,
      FullCertificate k β b (fun s => E (embedCoordinates e t s))) :
    LayerCertificate t b E k β (typeFamily t β (fun e => (C e).labels)) := by
  classical
  constructor
  · intro J hJ
    obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β (fun e => (C e).labels) J).1 hJ
    apply hE
    exact cube_embedCoordinates e le_rfl htβ.le (htβ.trans hβb).le ((C e).slopes L hL)
  · intro J hJ
    obtain ⟨e, L, hL, rfl⟩ := (mem_typeFamily t β (fun e => (C e).labels) J).1 hJ
    refine ⟨Finset.univ.map e, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      simpa only [Label.embed, embedCoordinates_apply] using (C e).slopes L hL j
    · intro i hi
      apply embedCoordinates_outside e t L.slope
      rintro ⟨j, rfl⟩
      exact hi (Finset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)
    · intro hk0
      omega
    · intro _
      exact Label.embed_normalized_offset e t β L
        ((C e).offsets L hL).tendsto_div_nhds_zero
    · exact typeFamily_approximatesOnSupport t β b E C e hL
  · exact typeFamily_supported_competitor t β (fun e => (C e).labels)
      (fun e => (C e).nonempty)

/-- The per-layer existence interface used by the finite threshold recursion.
The only input is the lower-dimensional full approximation theorem. -/
theorem exists_typeFamily_layerCertificate {k d : ℕ}
    (hk : 0 < k) (hkd : k < d) {t β b : ℝ}
    (htβ : t < β) (hβb : β < b)
    (E : (Fin d → ℝ) → ℝ)
    (hE : ∀ r, Cube t b r → 0 < E r)
    (hIH : ∀ E' : (Fin k → ℝ) → ℝ,
      (∀ s, Cube β b s → 0 < E' s) → Nonempty (FullCertificate k β b E')) :
    ∃ F : Finset (Label d), F.Nonempty ∧ LayerCertificate t b E k β F := by
  classical
  have hC (e : Fin k ↪ Fin d) :
      Nonempty (FullCertificate k β b (fun s => E (embedCoordinates e t s))) := by
    apply hIH
    intro s hs
    exact hE _ (cube_embedCoordinates e le_rfl htβ.le (htβ.trans hβb).le hs)
  let C (e : Fin k ↪ Fin d) := Classical.choice (hC e)
  exact ⟨typeFamily t β (fun e => (C e).labels),
    typeFamily_nonempty hkd.le t β _ (fun e => (C e).nonempty),
    typeFamily_layerCertificate hk htβ hβb E hE C⟩

end Problem326.Affine

end

end OAI

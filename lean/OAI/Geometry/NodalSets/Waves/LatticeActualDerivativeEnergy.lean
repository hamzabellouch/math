import OAI.Geometry.NodalSets.Elliptic.RescaledDerivativeMoments
import OAI.Geometry.NodalSets.Waves.LatticePlaneWaveEnergy

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma norm_square_le_two_sub_add {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a‖^2 ≤ 2*‖a-b‖^2+2*‖b‖^2 := by
  have h := norm_add_le (a-b) b
  rw [sub_add_cancel] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg a) h 2
  nlinarith [sq_nonneg (‖a-b‖-‖b‖)]

theorem lattice_actual_derivative_energy
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) {H : Set Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S : Coord → ℝ) (D U Q : Set Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0) (_ : H ⊆ D) (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ContDiff ℝ ∞ S → d ≤ k0 →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : Coord, ‖v‖ ≤ 2 → ∀ k : ℕ, k ≤ d →
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ k (normalizedRescaling
            (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
            (a.latticeSigma hUD n x) x) v‖^2 ≤ C := by
  obtain ⟨C,hC,hplane⟩ := lattice_planeWave_derivative_energy g hH hg hp d
  refine ⟨2+2*C,by positivity,?_⟩
  intro w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU hS hd
  filter_upwards [hplane w S D U Q m J K k0 a hHD hUD hUH hU hUb hQ hQU,
    a.lattice_full_jet_approximation hUD hU hUb hQ hQU hS 2 (by norm_num) 1 (by norm_num),
    a.estimates] with n hW he hest
  obtain ⟨hfin,hW⟩ := hW
  obtain ⟨hfin',he⟩ := he
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv k hk
  let W := a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x)
  let A := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
    (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x
  have hAs (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (A i) :=
    normalizedRescaling_smooth _ (hest (latticeFrame a.cover hUD n i.1,i.2)).1 _ _ _ _ _
  have hWs (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (W i) :=
    a.latticePlaneWaveCoefficient_smooth _ _ _ _ _
  have hk' : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  have hid (i : SourceGrid U n × Fin 3) :
      iteratedFDeriv ℝ k (fun z ↦ A i z-W i z) v =
        iteratedFDeriv ℝ k (A i) v-iteratedFDeriv ℝ k (W i) v := by
    change iteratedFDeriv ℝ k (A i-W i) v = _
    exact iteratedFDeriv_sub_apply ((hAs i).of_le hk').contDiffAt ((hWs i).of_le hk').contDiffAt
  have herr := he x hx _ (show 1 ≤ sourceSignScale g S x by
    linarith [a.source_sign_scale_lower x (hUD (hQU hx))]) v hv (⟨k,by omega⟩ : Fin (k0+1))
  change (∑ i, ‖iteratedFDeriv ℝ k (fun z ↦ A i z-W i z) v‖^2) ≤ 1 at herr
  simp_rw [hid] at herr
  have hw := hW x hx v k hk
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (SourceGrid U n × Fin 3))) ↦
    norm_square_le_two_sub_add (iteratedFDeriv ℝ k (A i) v) (iteratedFDeriv ℝ k (W i) v))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hb
  change (∑ i, ‖iteratedFDeriv ℝ k (A i) v‖^2) ≤ _
  change (∑ i, ‖iteratedFDeriv ℝ k (W i) v‖^2) ≤ C at hw
  linarith

end
end Yau.Geometry

end OAI

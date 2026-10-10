import OAI.Analysis.MassAction.LocalCertificateRadius
import OAI.Analysis.MassAction.AffineGlobalGluing

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326.Affine

/-- The exact gluing interface used by the dimension induction. Local certificates
are first extended to nearby minimum levels with a common stronger decay radius,
then the finite interval construction glues them into one full certificate. -/
theorem glue_localCertificates {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a ≤ b) (E : (Fin d → ℝ) → ℝ)
    (hlocal : ∀ t : ℝ, a ≤ t → t ≤ b →
      Nonempty (LocalCertificate d a b t E)) :
    Nonempty (FullCertificate d a b E) := by
  classical
  let I := {t : ℝ // t ∈ Icc a b}
  let C (t : I) : LocalCertificate d a b t.val E :=
    Classical.choice (hlocal t.val t.property.1 t.property.2)
  choose r hr hdecay happ using fun t : I => (C t).exists_radius hd
  let ρ (t : ℝ) : ℝ := if ht : t ∈ Icc a b then r ⟨t, ht⟩ else 1
  let Γ (t : ℝ) : Finset (Label d) :=
    if ht : t ∈ Icc a b then (C ⟨t, ht⟩).labels else ∅
  have hρ (t : ℝ) (ht : t ∈ Icc a b) : 0 < ρ t := by
    simpa only [ρ, dite_eq_left ht] using hr ⟨t, ht⟩
  have hbaseline (t : ℝ) (ht : t ∈ Icc a b) :
      (⟨fun _ => t, fun _ => 0⟩ : Label d) ∈ Γ t := by
    simpa only [Γ, dite_eq_left ht] using (C ⟨t, ht⟩).baseline
  have hdata (t : ℝ) (ht : t ∈ Icc a b) (L : Label d) (hL : L ∈ Γ t) :
      Cube a b L.slope ∧ HasMinimum L.slope t ∧
        L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ (t + ρ t)) := by
    have hLC : L ∈ (C ⟨t, ht⟩).labels := by
      simpa only [Γ, dite_eq_left ht] using hL
    refine ⟨?_, (C ⟨t, ht⟩).minima L hLC, ?_⟩
    · intro i
      have hi := (C ⟨t, ht⟩).slopes L hLC i
      exact ⟨ht.1.trans hi.1, hi.2⟩
    · simpa only [ρ, dite_eq_left ht] using hdecay ⟨t, ht⟩ L hLC
  have hnear (t : ℝ) (ht : t ∈ Icc a b) (μ : ℝ) (hμ : |μ - t| < ρ t) :
      ApproximatesAtMinimum (Γ t) a b μ E := by
    have hμ' : |μ - t| < r ⟨t, ht⟩ := by
      simpa only [ρ, dite_eq_left ht] using hμ
    simpa only [Γ, dite_eq_left ht] using happ ⟨t, ht⟩ μ hμ'
  obtain ⟨Λ, hΛ, hdataΛ, happΛ⟩ :=
    exists_approximating_family_of_local_families hd hab E ρ Γ hρ hbaseline hdata hnear
  exact ⟨{
    labels := Λ
    nonempty := hΛ
    slopes := fun L hL => (hdataΛ L hL).1
    offsets := fun L hL => (hdataΛ L hL).2
    approximation := happΛ
  }⟩

end Problem326.Affine

end

end OAI

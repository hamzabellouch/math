import OAI.Analysis.AncientFlat.Energy.EnergyEquation
import OAI.Analysis.AncientFlat.Energy.EnergyGronwall

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BoundedContinuousFunction Laplacian
namespace ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem homogeneous_unique (T α β C B : ℝ) (hT : 0<T) (hα : 0<α)
    (hC : 0≤C) (hB : 0≤B)
    (A : ℝ → V →ᵇ ℝ) (b : ℝ → V →ᵇ ℂ)
    (_hcA : ContinuousOn A (Icc 0 T)) (_hcb : ContinuousOn b (Icc 0 T))
    (hAb : ∀ t ∈ Icc 0 T, ∀ x, A t x ∈ Icc α β)
    (hb : ∀ t ∈ Icc 0 T, ‖b t‖≤B)
    (hA : ∀ t ∈ Icc 0 T, ContDiff ℝ 2 (A t : V → ℝ))
    (hAj : ∀ t ∈ Icc 0 T, ∀ n : ℕ, n≤2 → ∀ x, ‖iteratedFDeriv ℝ n (A t : V → ℝ) x‖≤C)
    (u : ℝ → V →ᵇ ℂ) (hu0 : u 0=0) (huc : ContinuousOn u (Icc 0 T))
    (hu : ∀ t ∈ Ioo 0 T, ContDiff ℝ 4 (u t : V → ℂ))
    (huj : ∀ ε R : ℝ, 0<ε → ε≤R → R<T → ∃ M : ℝ, 0≤M ∧
      ∀ t ∈ Icc ε R, ∀ n : ℕ, n≤4 → ∀ x, ‖iteratedFDeriv ℝ n (u t : V → ℂ) x‖≤M)
    (htime : ∀ t ∈ Ioo 0 T, ∃ v : V →ᵇ ℂ, HasDerivAt u v t ∧ ∀ x,
      v x = -(A t x : ℂ)*Δ (Δ (u t : V → ℂ)) x-b t x*u t x) :
    ∀ t ∈ Icc 0 T, u t=0 := by
  obtain ⟨K,hK0,hK⟩ := exists_energy_constant (V := V) α C hα hC
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ∃ d : ℝ, HasDerivAt (fun s => mass (u s : V → ℂ)) d t ∧
        d≤(2*K+2*B)*mass (u t : V → ℂ) := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le,ht.2.le⟩
    obtain ⟨M,hM,hMj⟩ := huj t t ht.1 le_rfl ht.2
    have hub : BoundedJets 4 (u t : V → ℂ) :=
      fun n hn => ⟨M,hM,hMj t ⟨le_rfl,le_rfl⟩ n hn⟩
    obtain ⟨v,hv,hveq⟩ := htime t ht
    refine ⟨2*pair (u t) v,hasDerivAt_mass hv,?_⟩
    exact energy_rhs_le hα hB (A t) (b t) (u t) v (hb t ht')
      (hA t ht') (hAj t ht') (fun x => (hAb t ht' x).1) (hu t ht) hub hK hveq
  have h0 : mass (u 0 : V → ℂ)=0 := by simp [hu0,mass]
  have he := nonneg_energy_eq_zero hT (continuousOn_mass huc) h0
    (fun t _ => mass_nonneg (u t : V → ℂ)) hd
  intro t ht
  exact mass_eq_zero_bcf (he t ht)
end ParametrixUniqueness

end

end OAI

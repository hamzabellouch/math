import OAI.Analysis.AncientFlat.Evolution.EvolutionAlgebra

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
open ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β s T C B : ℝ} {A : C(ℝ,V →ᵇ Icc α β)} {b : C(ℝ,V →ᵇ ℂ)}
  {d : C₀(V,ℂ)} {u v : ℝ → C₀(V,ℂ)}
omit [MeasurableSpace V] [BorelSpace V] in
lemma Evolves.restrict (hu : Evolves A b s T d u) {r : ℝ} (hr : s≤r) :
    Evolves A b r T (u r) u := by
  refine ⟨rfl,hu.2.1.mono (Icc_subset_Icc_left hr),?_,?_,?_⟩
  · intro t ht; exact hu.2.2.1 t ⟨hr.trans_lt ht.1,ht.2⟩
  · intro t ht; exact hu.2.2.2.1 t ⟨hr.trans_lt ht.1,ht.2⟩
  · intro t ht; exact hu.2.2.2.2 t ⟨hr.trans_lt ht.1,ht.2⟩
lemma Evolves.zero_unique (hu : Evolves A b s T 0 u) (hsT : s<T) (hα : 0<α)
    (hC : 0≤C) (hB : 0≤B)
    (hb : ∀ t ∈ Icc s T, ‖b t‖≤B)
    (hA : ∀ t ∈ Icc s T, ContDiff ℝ 2 (fun x => (A t x).val))
    (hAj : ∀ t ∈ Icc s T, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖≤C) :
    ∀ t ∈ Icc s T, u t=0 := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  obtain ⟨K,hK0,hK⟩ := exists_energy_constant (V := V) α C hα hC
  let w : ℝ → V →ᵇ ℂ := fun r => (u (s+r)).toBCF
  have hwc : ContinuousOn w (Icc 0 (T-s)) := by
    apply ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp_continuousOn
    apply hu.2.1.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change s+t ∈ Icc s T
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hw0 : mass (w 0 : V → ℂ)=0 := by simp [w,hu.1,mass]
  have hd (t : ℝ) (ht : t ∈ Ioo 0 (T-s)) :
      ∃ e : ℝ, HasDerivAt (fun r => mass (w r : V → ℂ)) e t ∧
        e≤(2*K+2*B)*mass (w t : V → ℂ) := by
    have hst : s+t ∈ Ioo s T := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have hst' : s+t ∈ Icc s T := ⟨hst.1.le,hst.2.le⟩
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 (s+t) hst
    have hwt : HasDerivAt w p t := by
      have ha : HasDerivAt (fun r : ℝ => s+r) 1 t := (hasDerivAt_id t).const_add s
      convert hp.scomp t ha using 1 <;> first | rfl | simp only [one_smul]
    have hj : BoundedJets 4 (w t : V → ℂ) := by
      intro n hn
      obtain ⟨M,hM⟩ := hu.2.2.2.1 (s+t) hst n hn
      exact ⟨max M 0,le_max_right _ _,fun x => (hM x).trans (le_max_left _ _)⟩
    let a : V →ᵇ ℝ := (A (s+t)).comp Subtype.val (LipschitzWith.subtype_val (Icc α β))
    refine ⟨2*pair (w t) p,hasDerivAt_mass hwt,?_⟩
    exact energy_rhs_le hα hB a (b (s+t)) (w t) p (hb _ hst') (hA _ hst')
      (hAj _ hst') (fun x => (A (s+t) x).property.1) (hu.2.2.1 _ hst) hj hK hpe
  have he := nonneg_energy_eq_zero (sub_pos.mpr hsT) (continuousOn_mass hwc) hw0
    (fun t _ => mass_nonneg (w t : V → ℂ)) hd
  intro t ht
  have ht' : t-s ∈ Icc 0 (T-s) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hh := mass_eq_zero_bcf (he (t-s) ht')
  apply ZeroAtInftyContinuousMap.toBCF_injective V ℂ
  change (u t).toBCF=0
  simpa [w] using hh
lemma Evolves.unique (hu : Evolves A b s T d u) (hv : Evolves A b s T d v)
    (hsT : s≤T) (hα : 0<α) (hC : 0≤C) (hB : 0≤B)
    (hb : ∀ t ∈ Icc s T, ‖b t‖≤B)
    (hA : ∀ t ∈ Icc s T, ContDiff ℝ 2 (fun x => (A t x).val))
    (hAj : ∀ t ∈ Icc s T, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖≤C) :
    ∀ t ∈ Icc s T, u t=v t := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  rcases hsT.eq_or_lt with he|hlt
  · subst T
    intro t ht
    have ht : t=s := le_antisymm ht.2 ht.1
    subst t
    exact hu.1.trans hv.1.symm
  · have hh : Evolves A b s T 0 (fun t => u t+(-1 : ℂ)•v t) := by
      simpa only [neg_smul,one_smul,add_neg_cancel] using hu.add (hv.smul (-1))
    have hz := hh.zero_unique hlt hα hC hB hb hA hAj
    intro t ht
    simpa only [neg_smul,one_smul,←sub_eq_add_neg,sub_eq_zero] using hz t ht
end ParametrixEvolution

end

end OAI

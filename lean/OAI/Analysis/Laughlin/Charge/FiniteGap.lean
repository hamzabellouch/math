import OAI.Analysis.Laughlin.Charge.Sectors
import Mathlib.Topology.Order.Compact

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

noncomputable def occupationState (Q : ℕ) (A : Finset (Fin (Q+1))) : Hilbert Q :=
  occupationEuclidean Q (occupationBasis Q A)

theorem occupationState_apply (Q : ℕ) (A B : Finset (Fin (Q+1))) :
    occupationState Q A B = if A=B then 1 else 0 := by
  change (occupationBasis Q).repr (occupationBasis Q A) B = _
  simp [Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationState_unit (Q n : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=n) :
    occupationState Q A ∈ unitSector Q n := by
  refine ⟨?_,?_⟩
  · intro B hB
    rw [occupationState_apply,ite_eq_right]
    intro he
    subst B
    exact hB hA
  · rw [occupationState,occupationEuclidean_norm]
    simp only [occupationNormSq,Module.Basis.repr_self,Finsupp.single_apply]
    rw [Finset.sum_eq_single A]
    · simp
    · intro B _ hBA
      simp [Ne.symm hBA]
    · simp

theorem occupationState_ne_zero (Q : ℕ) (A : Finset (Fin (Q+1))) :
    occupationState Q A ≠ 0 := by
  intro he
  have h := congrArg (fun x : Hilbert Q => x A) he
  simp [occupationState_apply] at h

theorem exists_unit_not_ground (Q n : ℕ) (hn : 0<n) (hN : n<Q+1)
    (hline : Module.finrank ℂ (groundKernel Q n)=1) :
    ∃ x ∈ unitSector Q n, x ∉ groundKernel Q n := by
  classical
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin (Q+1))).card by simpa using hN.le)
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<A.card by omega)
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show A.card < (Finset.univ : Finset (Fin (Q+1))).card by simpa [hcard] using hN)
  let B := insert b (A.erase a)
  have hB : B.card=n := by
    rw [Finset.card_insert_of_notMem (fun h => hb (Finset.mem_of_mem_erase h)),Finset.card_erase_of_mem ha]
    omega
  have hAB : A≠B := by
    intro he
    apply hb
    rw [he]
    exact Finset.mem_insert_self _ _
  by_contra h
  push Not at h
  have heA := h (occupationState Q A) (occupationState_unit Q n A hcard)
  have heB := h (occupationState Q B) (occupationState_unit Q n B hB)
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hline
    (x := (⟨occupationState Q A,heA⟩ : groundKernel Q n))
    (by intro hz; exact occupationState_ne_zero Q A (congrArg Subtype.val hz))
    (⟨occupationState Q B,heB⟩ : groundKernel Q n)
  have hcoord := congrArg (fun x : groundKernel Q n => (x : Hilbert Q) B) hc
  simp [occupationState_apply,hAB] at hcoord

theorem excited_unit_nonempty (Q n : ℕ) (hn : 0<n) (hN : n<Q+1)
    (hline : Module.finrank ℂ (groundKernel Q n)=1) :
    {x | x ∈ unitSector Q n ∧ x ∈ (groundKernel Q n)ᗮ}.Nonempty := by
  obtain ⟨x,hx,hxK⟩ := exists_unit_not_ground Q n hn hN hline
  let K := groundKernel Q n
  let v := x-K.starProjection x
  have hvK : v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  have hvS : v ∈ particleSector Q n := (particleSector Q n).sub_mem hx.1
    (K.starProjection_apply_mem x).1
  have hv : v≠0 := by
    intro hz
    have he : K.starProjection x=x := (sub_eq_zero.mp hz).symm
    exact hxK (K.starProjection_eq_self_iff.mp he)
  have hnorm : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  refine ⟨(‖v‖ : ℂ)⁻¹ • v,⟨(particleSector Q n).smul_mem _ hvS,?_⟩,Kᗮ.smul_mem _ hvK⟩
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hnorm]
  norm_num

theorem energy_continuous (Q : ℕ) : Continuous (energy Q) := by
  have he : energy Q = fun x => (inner ℂ (euclideanFockHamiltonian Q x) x).re := by
    funext x
    exact energy_eq_inner Q x
  rw [he]
  exact Complex.continuous_re.comp
    (((euclideanFockHamiltonian Q).continuous_of_finiteDimensional).inner continuous_id)

theorem excited_energy_pos (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ unitSector Q n ∧ x ∈ (groundKernel Q n)ᗮ) : 0<energy Q x := by
  have hn := energy_nonneg Q x
  by_contra h
  have he : energy Q x=0 := le_antisymm (le_of_not_gt h) hn
  have hxK : x ∈ groundKernel Q n := ⟨hx.1.1,(energy_eq_zero_iff Q x).mp he⟩
  have hi : inner ℂ x x=0 := (Submodule.mem_orthogonal _ _).mp hx.2 x hxK
  have hz : x=0 := inner_self_eq_zero.mp hi
  simpa [hz] using hx.1.2

theorem neutralGap_pos (Q n : ℕ) (hn : 0<n) (hN : n<Q+1)
    (hline : Module.finrank ℂ (groundKernel Q n)=1) : 0<neutralGap Q n := by
  let U := {x : Hilbert Q | x ∈ unitSector Q n ∧ x ∈ (groundKernel Q n)ᗮ}
  have heq : U = ((particleSector Q n : Set (Hilbert Q)) ∩
      ((groundKernel Q n)ᗮ : Set (Hilbert Q))) ∩ Metric.sphere 0 1 := by
    ext x
    simp only [U,unitSector,Set.mem_ofPred_eq,Set.mem_inter_iff,Metric.mem_sphere,dist_zero_right]
    constructor
    · rintro ⟨⟨hx,h1⟩,hK⟩
      refine ⟨⟨hx,hK⟩,?_⟩
      nlinarith [norm_nonneg x]
    · rintro ⟨⟨hx,hK⟩,h1⟩
      exact ⟨⟨hx,by rw [h1]; norm_num⟩,hK⟩
  have hcompact : IsCompact U := by
    rw [heq]
    exact (isCompact_sphere (0 : Hilbert Q) 1).inter_left
      ((particleSector Q n).closed_of_finiteDimensional.inter
        ((groundKernel Q n)ᗮ).closed_of_finiteDimensional)
  obtain ⟨x,hx,hmin⟩ := hcompact.exists_isMinOn
    (excited_unit_nonempty Q n hn hN hline) (energy_continuous Q).continuousOn
  have he : neutralGap Q n=energy Q x := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0,by rintro t ⟨v,hv,rfl⟩; exact energy_nonneg Q v⟩
      · exact ⟨x,hx,rfl⟩
    · apply le_csInf
      · exact (excited_unit_nonempty Q n hn hN hline).image _
      · rintro t ⟨v,hv,rfl⟩
        exact hmin hv
  rw [he]
  exact excited_energy_pos Q n x hx

end Laughlin.Charge

end OAI

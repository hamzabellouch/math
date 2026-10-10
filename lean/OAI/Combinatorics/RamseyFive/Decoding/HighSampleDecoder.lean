import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HighSampleGrowth

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def highDomain {n t : ℕ} (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V)) :
    Finset (SampleFlag (K:=K) (V:=V)) :=
  Finset.univ.filter fun z=>4≤finrank K (sampleSpan x z.2) ∧
    z.1.submodule≤(sampleSpan x z.2).dualCoannihilator

omit [Finite K] in
theorem highDomain_card (hdim : finrank K V=5) {n t : ℕ}
    (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V)) :
    (highDomain x).card≤Fintype.card (ℙ K (Dual K V)) := by
  apply Finset.card_le_card_of_injOn Prod.snd (t:=Finset.univ)
    (fun _ _=>Finset.mem_univ _) ?_
  intro z hz w hw he
  have hz':=(Finset.mem_filter.mp hz).2
  have hw':=(Finset.mem_filter.mp hw).2
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq (sampleSpan x z.2)
  rw [hdim] at hd
  have hl : finrank K (sampleSpan x z.2).dualCoannihilator≤1 := by omega
  have hzl : z.1.submodule=(sampleSpan x z.2).dualCoannihilator :=
    Submodule.eq_of_le_of_finrank_eq hz'.2 (by
      have hh:=Submodule.finrank_mono hz'.2
      rw [z.1.finrank_submodule] at hh ⊢
      omega)
  have hwl : w.1.submodule=(sampleSpan x z.2).dualCoannihilator := by
    have hwc : w.1.submodule≤(sampleSpan x z.2).dualCoannihilator := he ▸ hw'.2
    apply Submodule.eq_of_le_of_finrank_eq hwc
    have hh:=Submodule.finrank_mono hwc
    rw [w.1.finrank_submodule] at hh ⊢
    omega
  exact Prod.ext (Projectivization.submodule_injective (hzl.trans hwl.symm)) he

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma growSpan_le {n : ℕ} (y : ℙ K (Dual K V))
    (W U : Submodule K (Dual K V)) (x : Fin n→SampleFlag (K:=K) (V:=V))
    (hW : W≤U) (hx : ∀ i,Incident (x i).1 y → (x i).2.submodule≤U) :
    growSpan y W x≤U := by
  apply sup_le hW
  unfold Marking.state
  apply iSup₂_le
  intro i _
  split_ifs with hi
  · exact hx i hi
  · exact bot_le

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma runSpan_le {n t : ℕ} (y : ℙ K (Dual K V))
    (W U : Submodule K (Dual K V)) (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V))
    (hW : W≤U) (hx : ∀ j i,Incident (x j i).1 y → (x j i).2.submodule≤U) :
    runSamples (growSpan y) W x≤U := by
  induction t generalizing W with
  | zero=>exact hW
  | succ t ih=>
    exact ih (growSpan y W (x 0)) (fun j=>x j.succ)
      (growSpan_le y W U (x 0) hW (hx 0)) (fun j=>hx j.succ)

omit [Finite K] [FiniteDimensional K V] in
theorem mem_highDomain {n t : ℕ} (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V))
    (z : SampleFlag (K:=K) (V:=V)) (hz : Incident z.1 z.2)
    (hr : 4≤finrank K (sampleSpan x z.2))
    (hc : ∀ j i,Incident (x j i).1 z.2 → Incident z.1 (x j i).2) :
    z∈highDomain x := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr,?_⟩
  rw [←Submodule.le_dualAnnihilator_iff_le_dualCoannihilator]
  apply runSpan_le z.2 z.2.submodule z.1.submodule.dualAnnihilator x
    ((incident_iff_dualAnnihilator _ _).mp hz)
  intro j i hi
  exact (incident_iff_dualAnnihilator _ _).mp (hc j i hi)
end
end SharpRamseyFive.HighSamples

end OAI

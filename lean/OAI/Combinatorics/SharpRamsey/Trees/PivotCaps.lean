import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotFreshPair
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedPotential

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation ProjectiveDuality PublicTables TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def primalCap {h : ℕ} (U : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) : Finset (Projectivization K V) :=
  U.filter (fun x => pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) u (bidual x))

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma primalCap_image {h : ℕ} (U : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) :
    (primalCap U u).image (bidual (K:=K) (V:=V))=
      cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V))) u := by
  ext y
  simp only [primalCap,cap,mem_image,mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hp⟩
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,hp⟩,rfl⟩

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma primalCap_card {h : ℕ} (U : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) :
    (primalCap U u).card=
      (cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V))) u).card := by
  rw [←primalCap_image,card_image_of_injective _ (bidual (K:=K) (V:=V)).injective]

omit [Finite K] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma primalCap_capture {h : ℕ} (U S : Finset (Projectivization K V))
    (u : Fin h→Projectivization K (Module.Dual K V)) (M : ℝ)
    (hS : S⊆U)
    (hg : GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V)))
      (S.image (bidual (K:=K) (V:=V))) M u) :
    (99:ℝ)*S.card≤100*(S∩primalCap U u).card := by
  have hh := cap_capture (image_subset_image hS) hg
  have he : (S∩primalCap U u).image (bidual (K:=K) (V:=V))=
      (S.image (bidual (K:=K) (V:=V)))∩
        cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V))) u := by
    rw [image_inter _ _ (bidual (K:=K) (V:=V)).injective,primalCap_image]
  rw [←he,card_image_of_injective _ (bidual (K:=K) (V:=V)).injective,
    card_image_of_injective _ (bidual (K:=K) (V:=V)).injective] at hh
  exact hh

omit [Finite K] [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem accepted_caps {n h h' : ℕ}
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (z : Fin h→Projectivization K V) (u : Fin h'→Projectivization K (Module.Dual K V))
    (hz : implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (B∩UT) (2000*(Nat.card K:ℝ)^(n+3)/A.card)) z)
    (hu : implementAccept ((B∩UT)∩cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V)))
        ((A∩U).image (bidual (K:=K) (V:=V))) (2000*(Nat.card K:ℝ)^(n+3)/B.card)) u) :
    primalCap U u⊆U ∧ cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z⊆UT ∧
    ((primalCap U u).card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/B.card ∧
    ((cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z).card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/A.card ∧
    (99:ℝ)*(A∩U).card≤100*((A∩U)∩primalCap U u).card ∧
    (99:ℝ)*(B∩UT).card≤100*((B∩UT)∩cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z).card := by
  refine ⟨filter_subset _ _,filter_subset _ _,?_,hz.2.1,?_,cap_capture inter_subset_right hz.2⟩
  · rw [primalCap_card]
    exact hu.2.1
  · exact primalCap_capture U (A∩U) u _ inter_subset_right hu.2

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem accepted_branch {n h h' : ℕ}
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (z : Fin h→Projectivization K V) (u : Fin h'→Projectivization K (Module.Dual K V))
    (hz : implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (B∩UT) (2000*(Nat.card K:ℝ)^(n+3)/A.card)) z)
    (hu : implementAccept ((B∩UT)∩cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) (U.image (bidual (K:=K) (V:=V)))
        ((A∩U).image (bidual (K:=K) (V:=V))) (2000*(Nat.card K:ℝ)^(n+3)/B.card)) u) :
    let Q := (Nat.card K:ℝ)^(n+3)
    ExecutedPotential.potential Q (primalCap U u,UT)+
      ExecutedPotential.potential Q (U,cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z)≤
      ExecutedPotential.potential Q (U,UT)+(b+log 4+2*log 2000) := by
  have hv := accepted_caps A U W B UT z u hz hu
  apply ExecutedPotential.branch _ 2000 b _ (by norm_num) (U,UT)
    (primalCap U u,cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z) A B hA hB htrimA htrimB hprod hv.2.2.1 hv.2.2.2.1
  exact pow_pos (by exact_mod_cast Nat.card_pos (α:=K)) _

end
end SharpLogRamsey.PivotGeometry

end

end OAI

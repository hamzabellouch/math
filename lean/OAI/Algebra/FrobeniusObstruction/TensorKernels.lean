import Mathlib
import OAI.Algebra.FrobeniusObstruction.TensorCohomology
import OAI.Algebra.FrobeniusObstruction.CycleTransfer

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction

variable {k : Type*} [Field k]

private theorem generalized_inverse {V : Type*} [AddCommGroup V] [Module k V]
    (S : V →ₗ[k] V) : ∃ L : V →ₗ[k] V, ∀ x, S (L (S x)) = S x := by
  obtain ⟨g,hg⟩ := S.rangeRestrict.exists_rightInverse_of_surjective S.range_rangeRestrict
  obtain ⟨h,hh⟩ := S.range.subtype.exists_leftInverse_of_injective S.range.ker_subtype
  refine ⟨g.comp h, fun x => ?_⟩
  have hx : h (S x) = S.rangeRestrict x :=
    LinearMap.congr_fun hh (S.rangeRestrict x)
  change S (g (h (S x))) = S x
  rw [hx]
  exact congrArg Subtype.val (LinearMap.congr_fun hg (S.rangeRestrict x))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

                                                                       
                             
def kernelTensorSpace (S : ∀ i, V i →ₗ[k] V i) (J : Finset ι) :
    Submodule k (⨂[k] i, V i) :=
  Submodule.span k {z | ∃ m : ∀ i, V i,
    (∀ i ∈ J, S i (m i) = 0) ∧ PiTensorProduct.tprod k m = z}

                                         
def tensorAction (S : ∀ i, V i →ₗ[k] V i) (I : Finset ι) :
    (⨂[k] i, V i) →ₗ[k] (⨂[k] i, V i) :=
  PiTensorProduct.map fun i => if i ∈ I then S i else LinearMap.id

                                                                             
                                                                            
                                                                        
theorem joint_tensor_kernel (S : ∀ i, V i →ₗ[k] V i) (active : Finset ι) :
    (⨅ (I : Finset ι) (_ : I ⊆ active) (_ : I.card = 3),
      LinearMap.ker (tensorAction V S I)) =
    (⨆ (J : Finset ι) (_ : J ⊆ active) (_ : (active \ J).card ≤ 2),
      kernelTensorSpace V S J) := by
  classical
  let R := ⨆ (J : Finset ι) (_ : J ⊆ active) (_ : (active \ J).card ≤ 2),
      kernelTensorSpace V S J
  have hR (J : Finset ι) (hJ : J ⊆ active) (hc : (active \ J).card ≤ 2) :
      kernelTensorSpace V S J ≤ R := le_iSup_of_le J (le_iSup_of_le hJ (le_iSup_of_le hc le_rfl))
  apply le_antisymm
  · intro x hx
    have hz (I : Finset ι) (hI : I ⊆ active) (hcard : I.card = 3) :
        tensorAction V S I x = 0 := by
      exact ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx I) hI) hcard)
    choose L hL using fun i => generalized_inverse (S i)
    let Q (i : ι) := (L i).comp (S i)
    let P (i : ι) := LinearMap.id - Q i
    have hSP (i : ι) (v : V i) : S i (P i v) = 0 := by
      change S i (v - L i (S i v)) = 0
      rw [map_sub, hL, sub_self]
    let F (A : Finset ι) := PiTensorProduct.map fun i => if i ∈ A then Q i else P i
    have hsum : ∑ A : Finset ι, F A = LinearMap.id := by
      apply PiTensorProduct.ext
      ext m
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, LinearMap.id_apply]
      simp only [F, PiTensorProduct.map_tprod]
      have hm : (fun i => Q i (m i)) + (fun i => P i (m i)) = m := by
        funext i
        change Q i (m i) + (m i - Q i (m i)) = m i
        abel
      conv_rhs => rw [← hm, (PiTensorProduct.tprod k).map_add_univ]
      apply Finset.sum_congr rfl
      intro A ha
      congr 1
      funext i
      simp only [Finset.piecewise]
      split_ifs <;> rfl
    have hFx (A : Finset ι) : F A x ∈ R := by
      by_cases hc : (active ∩ A).card ≤ 2
      · let J := active \ A
        have hJ : J ⊆ active := Finset.sdiff_subset
        have hjc : (active \ J).card ≤ 2 := by
          simpa only [J, Finset.sdiff_sdiff_self_left] using hc
        apply hR J hJ hjc
        clear hx hz
        induction x using PiTensorProduct.induction_on with
        | smul_tprod c m =>
          rw [map_smul]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          refine ⟨fun i => (if i ∈ A then Q i else P i) (m i), ?_, ?_⟩
          · intro i hi
            have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
            simpa only [ite_eq_right hiA] using hSP i (m i)
          · exact (PiTensorProduct.map_tprod _ _).symm
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      · have hc' : 3 ≤ (active ∩ A).card := by omega
        obtain ⟨I,hI,hcard⟩ := Finset.exists_subset_card_eq hc'
        have hIa : I ⊆ active := fun i hi => (Finset.mem_inter.mp (hI hi)).1
        have hIA : I ⊆ A := fun i hi => (Finset.mem_inter.mp (hI hi)).2
        let H := PiTensorProduct.map fun i =>
          if i ∈ I then L i else if i ∈ A then Q i else P i
        have hcomp : F A = H.comp (tensorAction V S I) := by
          dsimp only [F, H, tensorAction]
          rw [← PiTensorProduct.map_comp]
          congr 1
          funext i
          by_cases hi : i ∈ I
          · simp only [ite_eq_left hi, ite_eq_left (hIA hi), Q]
          · simp only [ite_eq_right hi, LinearMap.comp_id]
        rw [hcomp, LinearMap.comp_apply, hz I hIa hcard, map_zero]
        exact R.zero_mem
    change x ∈ R
    have hsx := LinearMap.congr_fun hsum x
    simp only [LinearMap.sum_apply, LinearMap.id_apply] at hsx
    rw [← hsx]
    exact Submodule.sum_mem R (fun A _ => hFx A)
  · refine iSup_le fun J => iSup_le fun hJ => iSup_le fun hc => ?_
    refine le_iInf fun I => le_iInf fun hI => le_iInf fun hcard => ?_
    apply Submodule.span_le.mpr
    rintro z ⟨m,hm,rfl⟩
    have hex : ∃ i ∈ I, i ∈ J := by
      by_contra hn
      have hsub : I ⊆ active \ J := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨hI hi, fun hij => hn ⟨i,hi,hij⟩⟩
      have := Finset.card_le_card hsub
      omega
    obtain ⟨i,hiI,hiJ⟩ := hex
    change tensorAction V S I (PiTensorProduct.tprod k m) = 0
    rw [tensorAction, PiTensorProduct.map_tprod]
    apply (PiTensorProduct.tprod k).map_coord_zero i
    simpa only [ite_eq_left hiI] using hm i hiJ

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction
open scoped BigOperators TensorProduct

variable {k ι : Type*} [Field k] [Fintype ι] [LinearOrder ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

                                                                       
                                                                       
                                                                           
theorem select_special_fiber_tensor
    (S P D r h : SignedTensor.EndFamily (k := k) V)
    (active : Finset ι) (hcard : 5 ≤ active.card)
    (hP2 : ∀ i, P i * P i = 1)
    (hDP : ∀ i, D i * P i = -(P i * D i))
    (hDr : ∀ i, D i * r i = r i * D i)
    (hPr : ∀ i, P i * r i = r i * P i)
    (hPh : ∀ i, P i * h i = -(h i * P i))
    (hDh : ∀ i, D i * h i + h i * D i = 1 - r i)
    (hNr : ∀ i ∈ active, ∀ x, S i x = 0 →
      S i (r i x) = 0 ∧ S i (D i (r i x)) = 0)
    (φ : (⨂[k] i, V i) →ₗ[k] k)
    (hφD : ∀ x, φ (SignedTensor.differential V P D x) = 0)
    (z : ⨂[k] i, V i)
    (hDz : SignedTensor.differential V P D z = 0)
    (hφz : φ z ≠ 0)
    (hz : ∀ I : Finset ι, I ⊆ active → I.card = 3 → tensorAction V S I z = 0) :
    ∃ (J : Finset ι) (m : ∀ i, V i),
      J ⊆ active ∧ 3 ≤ J.card ∧
      (∀ i ∈ J, S i (m i) = 0 ∧ S i (D i (m i)) = 0) ∧
      φ (PiTensorProduct.tprod k m) ≠ 0 := by
  classical
  let Good : Set (⨂[k] i, V i) := {x | ∃ (J : Finset ι) (m : ∀ i, V i),
    J ⊆ active ∧ (active \ J).card ≤ 2 ∧
    (∀ i ∈ J, S i (m i) = 0 ∧ S i (D i (m i)) = 0) ∧
    PiTensorProduct.tprod k m = x}
  let T := Submodule.span k Good
  have hm : (⨅ (I : Finset ι) (_ : I ⊆ active) (_ : I.card = 3),
      LinearMap.ker (tensorAction V S I)) ≤ T.comap (PiTensorProduct.map r) := by
    rw [joint_tensor_kernel]
    refine iSup_le fun J => iSup_le fun hJ => iSup_le fun hJc => ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    change PiTensorProduct.map r (PiTensorProduct.tprod k m) ∈ T
    rw [PiTensorProduct.map_tprod]
    apply Submodule.subset_span
    refine ⟨J,fun i => r i (m i),hJ,hJc,?_,rfl⟩
    intro i hi
    exact hNr i (hJ hi) (m i) (hm i hi)
  have hzmem : z ∈ (⨅ (I : Finset ι) (_ : I ⊆ active) (_ : I.card = 3),
      LinearMap.ker (tensorAction V S I)) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    exact hz
  have hRz : PiTensorProduct.map r z ∈ T := hm hzmem
  have hpair : φ (PiTensorProduct.map r z) = φ z := by
    have H := LinearMap.congr_fun
      (SignedTensor.tensor_homotopy P D r h hP2 hDP hDr hPr hPh hDh) z
    change SignedTensor.differential V P D (SignedTensor.homotopy V P r h z) +
      SignedTensor.homotopy V P r h (SignedTensor.differential V P D z) =
        z - PiTensorProduct.map r z at H
    have Hφ := congrArg φ H
    rw [hDz, map_zero, add_zero, hφD, map_sub] at Hφ
    exact (sub_eq_zero.mp Hφ.symm).symm
  have hex : ∃ x ∈ Good, φ x ≠ 0 := by
    by_contra hn
    have hle : T ≤ LinearMap.ker φ := by
      apply Submodule.span_le.mpr
      intro x hx
      change φ x = 0
      by_contra hnx
      exact hn ⟨x,hx,hnx⟩
    apply hφz
    rw [← hpair]
    exact hle hRz
  obtain ⟨_,⟨J,m,hJ,hJc,hm,rfl⟩,hp⟩ := hex
  refine ⟨J,m,hJ,?_,hm,hp⟩
  have hc := Finset.card_sdiff_of_subset hJ
  have hle := Finset.card_le_card hJ
  omega

end BoundaryOnly.FormalObstruction

end

end OAI

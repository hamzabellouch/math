import Mathlib
import OAI.Analysis.HardSphere.Paths.Admissible
import OAI.Analysis.HardSphere.Allocation.PhysicalGroupComparison
import OAI.Analysis.HardSphere.Orbitals.PhysicalOrbitalReference

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma measureAffinity_nsmul {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] (n : ℕ) :
    measureAffinity (n • P) (n • Q)=(n:ℝ)*measureAffinity P Q := by
  have h := measureAffinity_smul P Q (n:ℝ) (Nat.cast_nonneg n)
  rw [ENNReal.ofReal_natCast] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

lemma affinity_double_sum_bound {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
    (A : I→J→Bool→Measure X) (Q : Bool→Measure X) (n : ℕ)
    [∀i j b,IsFiniteMeasure (A i j b)] [∀b,IsFiniteMeasure (Q b)]
    (h : ∀b,(∑i,∑j,A i j b)≤n • Q b) :
    (∑i,∑j,measureAffinity (A i j true) (A i j false))≤(n:ℝ)*measureAffinity (Q true) (Q false) := by
  have hb : (∑i,∑j,measureAffinity (A i j true) (A i j false))≤
      measureAffinity (∑i,∑j,A i j true) (∑i,∑j,A i j false) := by
    refine (Finset.sum_le_sum (fun i _ ↦ measureAffinity_finset_sum Finset.univ (fun j ↦ A i j true) (fun j ↦ A i j false))).trans ?_
    exact measureAffinity_finset_sum Finset.univ (fun i ↦ ∑j,A i j true) (fun i ↦ ∑j,A i j false)
  exact hb.trans ((measureAffinity_mono _ _ _ _ (h true) (h false)).trans_eq (measureAffinity_nsmul _ _ n))

lemma physical_total_posts {N K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (b : Bool)
    (P : Measure (Torus L×Configuration N L)) [SFinite P] :
    (∑ij : DiscreteTorus K×DiscreteTorus K,
      physicalCellVolumePost L (siteIndex (if b then ij.2 else ij.1))
        (siteIndex (if b then ij.1 else ij.2)) b ∘ₘ P)=
      (P.prod volume).map (cellObservation b) := by
  rw [Fintype.sum_prod_type]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [Finset.sum_comm]
    have he := physical_cell_posts_sum hL hK false P
    rw [←he]
    exact (siteIndexEquiv.sum_comp (fun tag : Fin 3→Fin K ↦
      ∑extra : DiscreteTorus K,physicalCellVolumePost L (siteIndex extra) tag false ∘ₘ P)).trans
      (Finset.sum_congr rfl (fun tag _ ↦ siteIndexEquiv.sum_comp
        (fun extra : Fin 3→Fin K ↦ physicalCellVolumePost L extra tag false ∘ₘ P)))
  · rw [←physical_cell_posts_sum hL hK true P]
    exact (siteIndexEquiv.sum_comp (fun tag : Fin 3→Fin K ↦
      ∑extra : DiscreteTorus K,physicalCellVolumePost L (siteIndex extra) tag true ∘ₘ P)).trans
      (Finset.sum_congr rfl (fun tag _ ↦ siteIndexEquiv.sum_comp
        (fun extra : Fin 3→Fin K ↦ physicalCellVolumePost L extra tag true ∘ₘ P)))

lemma physicalGroupReference_finite {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (x y : DiscreteTorus K) (g : Fin G) (b : Bool) :
    IsFiniteMeasure (physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b) := by
  let (flags : Fin (N+1)→Bool) (a : GridAllocation (N+1) K (G*M)) :=
    physicalBranchLaw_finite hL hK hψ g flags a m R C S s₀ (2*t) (by linarith) u
  unfold physicalGroupReference
  infer_instance

lemma physical_group_references_le {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (x y : DiscreteTorus K) (b : Bool) :
    (∑g : Fin G,physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b)≤
      (N+1) • (physicalCellVolumePost L (siteIndex (if b then y else x))
        (siteIndex (if b then x else y)) b ∘ₘ
        (((volume : Measure (Torus L)).prod volume).withDensity
          (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2)))) := by
  simpa only [physicalGroupReference,physicalObservedReference,physicalTaggedReference,
    branchParticles,Function.Embedding.subtype,Function.Embedding.coeFn_mk] using
    physical_all_references_le (M:=M) (G:=G) hL hK h50 hψ m R C S s₀ t ht u
      (siteIndex (if b then y else x)) (siteIndex (if b then x else y)) b

lemma physical_reference_sum_bound {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time) (b : Bool) :
    (∑ij : DiscreteTorus K×DiscreteTorus K,∑g : Fin G,
      physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u b)≤
      (N+1) • ((((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2))).prod volume).map (cellObservation b) := by
  let P : Measure (Torus L×Configuration N L) := (volume.prod volume).withDensity
    (fun p ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2))
  have hf := ((Lp.memLp ψ.1).comp_measurePreserving (cons_preserving (n:=N) L)).norm
  have hf' := hf.comp_measurePreserving (Measure.measurePreserving_swap (μ:=volume) (ν:=volume))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal
    ((memLp_two_iff_integrable_sq hf'.aestronglyMeasurable).1 hf').2
  change _≤(N+1) • (P.prod volume).map (cellObservation b)
  rw [←physical_total_posts hL hK b P,Finset.smul_sum]
  exact Finset.sum_le_sum (fun ij _ ↦ physical_group_references_le hL hK h50 hψ m t R C S s₀ ht u ij.1 ij.2 b)

attribute [local irreducible] physicalGroupReference physicalCellVolumePost

theorem physical_affinity_sum_bound {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time) :
    (∑ij : DiscreteTorus K×DiscreteTorus K,∑g : Fin G,
      measureAffinity (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)) ≤
      (N+1:ℝ)*(∫Y : Configuration N L,(∫x : Torus L,‖ψ.1 (Fin.cons x Y)‖)^2) := by
  classical
  let P : Measure (Torus L×Configuration N L) := (volume.prod volume).withDensity
    (fun p ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2))
  let Q := fun b ↦ (P.prod volume).map (cellObservation b)
  let A := fun ij : DiscreteTorus K×DiscreteTorus K ↦ fun g : Fin G ↦ fun b ↦
    physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u b
  have hm : Measurable (fun p : Configuration N L×Torus L ↦ ‖ψ.1 (Fin.cons p.2 p.1)‖) :=
    ((Lp.stronglyMeasurable ψ.1).measurable.comp (cons_preserving (n:=N) L).measurable).norm
  have hf := ((Lp.memLp ψ.1).comp_measurePreserving (cons_preserving (n:=N) L)).norm
  have hf' := hf.comp_measurePreserving (Measure.measurePreserving_swap (μ:=volume) (ν:=volume))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal
    ((memLp_two_iff_integrable_sq hf'.aestronglyMeasurable).1 hf').2
  let (ij : DiscreteTorus K×DiscreteTorus K) (g : Fin G) (b : Bool) : IsFiniteMeasure (A ij g b) :=
    physicalGroupReference_finite hL hK hψ m t R C S s₀ ht u ij.1 ij.2 g b
  have hsall (b : Bool) : (∑ij,∑g,A ij g b)≤(N+1) • Q b :=
    physical_reference_sum_bound hL hK h50 hψ m t R C S s₀ ht u b
  have hnorm : measureAffinity (Q true) (Q false)=
      ∫Y : Configuration N L,(∫x : Torus L,‖ψ.1 (Fin.cons x Y)‖)^2 :=
    physical_unrestricted_affinity (n:=N) (volume : Measure (Torus L)) (volume : Measure (Configuration N L))
      (fun p : Configuration N L×Torus L ↦ ‖ψ.1 (Fin.cons p.2 p.1)‖) hm hf (fun _ ↦ norm_nonneg _)
  have hb := affinity_double_sum_bound A Q (N+1) hsall
  simpa only [hnorm,Nat.cast_add,Nat.cast_one] using hb

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma pair_group_sum_lower {K G : ℕ} (hK : 400≤K) [NeZero K]
    (f : (DiscreteTorus K×DiscreteTorus K)→Fin G→ℝ) {B : ℝ} (hB : 0<B)
    (hf : ∀i g,0≤f i g)
    (hgain : ∀i∈currentAdmissiblePairs K,∀g,1/(8*B)≤f i g) :
    (K:ℝ)^6*(G:ℝ)/(16000*B)≤∑i,∑g,f i g := by
  have hc : (K:ℝ)^6≤2000*((currentAdmissiblePairs K).card:ℝ) := by
    exact_mod_cast current_admissible_card hK
  have hs : ((currentAdmissiblePairs K).card:ℝ)*(G:ℝ)/(8*B)≤
      ∑i∈currentAdmissiblePairs K,∑g,f i g := by
    calc
      _ = ∑i∈currentAdmissiblePairs K,∑g : Fin G,1/(8*B) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun g _ ↦ hgain i hi g))
  refine le_trans ?_ (hs.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ Finset.sum_nonneg (fun g _ ↦ hf i g))))
  apply (div_le_div_iff₀ (by positivity : 0<16000*B) (by positivity : 0<8*B)).mpr
  have hc' := mul_le_mul_of_nonneg_right hc (by positivity : 0≤(G:ℝ))
  nlinarith

lemma modulus_numeric_gain {V D I ell M B G : ℝ}
    (hV : 0<V) (hD : 0<D) (hell : 0<ell) (hM : 0<M) (hB : 0<B)
    (hG : ell/(8*M)≤G/D) (hbound : V^2*G/(16000*B)≤(D*V)*I) :
    ell/(128000*M*B)≤I/V := by
  calc
    _ = (ell/(8*M))/(16000*B) := by field_simp; ring
    _ ≤ (G/D)/(16000*B) := div_le_div_of_nonneg_right hG (by positivity)
    _ = (V^2*G/(16000*B))/((D*V)*V) := by field_simp
    _ ≤ ((D*V)*I)/((D*V)*V) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = I/V := by field_simp

theorem physical_modulus_from_gains {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 400≤K)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (D ell B : ℝ) (hDeq : D=(N+1:ℝ)/L.val^3) (hell : 0<ell) (hM : 0<M) (hB : 1≤B)
    (hG : ell/(8*M)≤(G:ℝ)/D)
    (hgain : ∀ij∈currentAdmissiblePairs K,∀g : Fin G,
      1/(8*B)≤ measureAffinity
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)) :
    ell/(128000*M*B)≤Phase.modulusOccupation
      (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  have h1 : 1≤K := by omega
  have h50 : 50<L.val := by rw [hL]; exact_mod_cast (show 50<K by omega)
  have hDp : 0<D := by rw [hDeq]; positivity
  let f := fun ij : DiscreteTorus K×DiscreteTorus K ↦ fun g : Fin G ↦
    measureAffinity
      (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
      (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)
  have hl := pair_group_sum_lower hK f (by linarith : 0<B)
    (fun _ _ ↦ affinity_nonneg _ _) hgain
  have hu := physical_affinity_sum_bound (M:=M) (G:=G) hL h1 h50 hψ m t R C S s₀ ht u
  have hbound : (L.val^3)^2*(G:ℝ)/(16000*B)≤
      (D*L.val^3)*(∫Y : Configuration N L,(∫x : Torus L,‖ψ.1 (Fin.cons x Y)‖)^2) := by
    have he : D*L.val^3=(N+1:ℝ) := by rw [hDeq]; field_simp
    rw [he]
    calc
      _ = (K:ℝ)^6*(G:ℝ)/(16000*B) := by rw [hL,←pow_mul]
      _ ≤ _ := hl.trans hu
  have H := modulus_numeric_gain (by positivity : 0<L.val^3) hDp hell
    (by exact_mod_cast hM) (by linarith : 0<B) hG hbound
  simpa only [Phase.modulusOccupation,Measure.real,BathSlice.volume_torus,
    ENNReal.toReal_ofReal (by positivity : 0≤L.val^3)] using H

end HardSphere.Groups
end
end

end OAI

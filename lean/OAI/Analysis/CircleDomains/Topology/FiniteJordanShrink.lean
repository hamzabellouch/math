import OAI.Analysis.CircleDomains.Topology.JordanDiskCompression
import OAI.Analysis.CircleDomains.Topology.FiniteSupportedHomeomorphs

namespace OAI

/-! One actual finite shrinking step. A disjoint Jordan cover with
boundaries avoiding the compact obstacle can be compressed so that all
its connected components have arbitrarily small image diameter. -/
open Set Metric Function
noncomputable section
namespace CircleDomainRigidity

lemma exists_finite_jordan_shrink
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ) {K : Set ℂ}
    (hK : IsCompact K)
    (hd : Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
      (closure (jordanInterior (H j)))))
    (hcover : K ⊆ ⋃ i, jordanInterior (H i))
    (havoid : ∀ i, Disjoint K (frontier (jordanInterior (H i))))
    {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℂ ≃ₜ ℂ,
      (∀ z ∉ ⋃ i, jordanInterior (H i), F z=z) ∧
      (∀ i, MapsTo F (jordanInterior (H i)) (jordanInterior (H i))) ∧
      ∀ x ∈ K, ∀ y ∈ connectedComponentIn K x,
        ∀ z ∈ connectedComponentIn K x, dist (F y) (F z)<ε := by
  classical
  let := Fintype.ofFinite I
  let A (i : I) := K ∩ closure (jordanInterior (H i))
  have hA (i : I) : IsCompact (A i) := hK.inter_right isClosed_closure
  have hAD (i : I) : A i ⊆ jordanInterior (H i) := by
    intro z hz
    by_contra hn
    have hf : z ∈ frontier (jordanInterior (H i)) := by
      rw [(jordanInterior_isOpen (H i)).frontier_eq]
      exact ⟨hz.2,hn⟩
    exact Set.disjoint_left.mp (havoid i) hz.1 hf
  choose f hfix hsmall using fun i => exists_compression_in_jordan_disk
    (H i) (hA i) (hAD i) (half_pos hε)
  have hdisj : Pairwise (fun i j => Disjoint (jordanInterior (H i))
      (jordanInterior (H j))) := fun i j hij =>
    (hd hij).mono subset_closure subset_closure
  obtain ⟨F,hFfix,hFon⟩ := finite_supported_homeomorphs Finset.univ
    (fun i => jordanInterior (H i)) f
    (fun i _ j _ hij => hdisj hij) (fun i _ => hfix i)
  have hF (i : I) (z : ℂ) (hz : z ∈ jordanInterior (H i)) : F z=f i z :=
    hFon i (Finset.mem_univ _) z hz
  refine ⟨F,?_,?_,?_⟩
  · intro z hz
    apply hFfix z
    simpa only [Finset.mem_univ, iUnion_true] using hz
  · intro i z hz
    rw [hF i z hz]
    exact _root_.OAI.Homeomorph.mapsTo_of_fixes_compl (f i) (hfix i) hz
  · intro x hx y hy z hz
    have hc : IsConnected (connectedComponentIn K x) :=
      isConnected_connectedComponentIn_iff.mpr hx
    obtain ⟨i,_,hi⟩ := connected_subset_one_of_disjoint_open_cover hc univ
      (fun i => jordanInterior (H i)) (fun i _ => jordanInterior_isOpen (H i))
      (fun i _ j _ hij => hdisj hij) (by
        simpa only [mem_univ, iUnion_true] using
          (connectedComponentIn_subset K x).trans hcover)
    have hyD := hi hy
    have hzD := hi hz
    rw [hF i y hyD,hF i z hzD]
    have hyA : y ∈ A i := ⟨connectedComponentIn_subset _ _ hy,subset_closure hyD⟩
    have hzA : z ∈ A i := ⟨connectedComponentIn_subset _ _ hz,subset_closure hzD⟩
    have h1 := hsmall i y hyA
    have h2 := hsmall i z hzA
    have ht := dist_triangle (f i y) (H i 0) (f i z)
    rw [dist_comm (f i z) (H i 0)] at h2
    linarith

lemma supported_displacement_bound
    {X Y I : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (F : X ≃ₜ X) (p : X → Y) (D : I → Set X) {δ : ℝ} (hδ : 0<δ)
    (hfix : ∀ x ∉ ⋃ i, D i, F x=x)
    (hmaps : ∀ i, MapsTo F (D i) (D i))
    (hosc : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, dist (p x) (p y)<δ) :
    ∀ x, dist (p (F x)) (p x)<δ := by
  intro x
  by_cases hx : x ∈ ⋃ i, D i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hosc i (F x) (hmaps i hi) x hi
  · rw [hfix x hx,dist_self]
    exact hδ

end CircleDomainRigidity

end

end OAI

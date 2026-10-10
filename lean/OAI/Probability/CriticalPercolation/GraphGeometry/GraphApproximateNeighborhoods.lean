import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.GraphNeighborhoodCompact
import OAI.Probability.CriticalPercolation.Growth.SparseDoubling

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def displacement (o : X) (r : ℕ) : Set (Γ ≃g Γ) :=
  {g | g o∈reachBall Γ o r}

lemma reachBall_mono (o : X) : Monotone (reachBall Γ o) := by
  intro r s hrs x hx
  obtain ⟨p,hp⟩ := hx
  exact ⟨p,hp.trans hrs⟩

lemma iso_reachBall_image (g : Γ ≃g Γ) (o : X) (r : ℕ) :
    g '' reachBall Γ o r=reachBall Γ (g o) r := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact iso_reachBall Γ g hy
  · intro x hx
    refine ⟨g.symm x,?_,g.apply_symm_apply x⟩
    simpa using iso_reachBall Γ g.symm hx

lemma reachBall_ncard_eq (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o x : X) (r : ℕ) :
    (reachBall Γ x r).ncard=(reachBall Γ o r).ncard := by
  obtain ⟨g,rfl⟩ := ht o x
  rw [←iso_reachBall_image Γ g o r,Set.ncard_image_of_injective _ g.injective]

lemma one_mem_displacement (o : X) (r : ℕ) : 1∈displacement Γ o r :=
  reachBall_self Γ o r

lemma displacement_inv {o : X} {r : ℕ} {g : Γ ≃g Γ} :
    g⁻¹∈displacement Γ o r ↔ g∈displacement Γ o r := by
  constructor
  · intro h
    change g o∈reachBall Γ o r
    simpa using inverse_displacement Γ g.symm h
  · exact inverse_displacement Γ g

lemma displacement_mul_subset (o : X) (r s : ℕ) :
    displacement Γ o r * displacement Γ o s ⊆ displacement Γ o (r+s) := by
  rintro g ⟨a,ha,b,hb,rfl⟩
  exact reachBall_add Γ ha (iso_reachBall Γ a hb)

lemma reachBall_packing (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    ∃ F : Finset X, (↑F : Set X)⊆reachBall Γ o (4*r) ∧ F.card≤K ∧
      ∀ u∈reachBall Γ o (4*r), ∃ v∈F, u∈reachBall Γ v (2*r) := by
  let A := (reachBall_finite Γ hl o (4*r)).toFinset
  let C : Finset (Finset X) := A.powerset.filter
    (fun F => (F : Set X).PairwiseDisjoint (fun v => reachBall Γ v r))
  obtain ⟨F,hFmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hFmax
  obtain ⟨hFA,hF⟩ := hFmax.1
  have hFo : (F : Set X)⊆reachBall Γ o (4*r) := by
    intro u hu
    exact (reachBall_finite Γ hl o (4*r)).mem_toFinset.mp (hFA hu)
  have hsub : (⋃ u∈(F : Set X), reachBall Γ u r) ⊆ reachBall Γ o (5*r) := by
    intro v hv
    obtain ⟨u,hu,hv⟩ := Set.mem_iUnion₂.mp hv
    simpa only [show 4*r+r=5*r by omega] using reachBall_add Γ (hFo hu) hv
  have hcount : F.card*(reachBall Γ o r).ncard≤(reachBall Γ o (5*r)).ncard := by
    calc
      F.card*(reachBall Γ o r).ncard = ∑ u∈F, (reachBall Γ u r).ncard := by
        symm
        apply Finset.sum_const_nat
        intro u _
        exact reachBall_ncard_eq Γ ht o u r
      _ = (⋃ u∈(F : Set X), reachBall Γ u r).ncard := by
        rw [(F.finite_toSet).ncard_biUnion (fun u _ => reachBall_finite Γ hl u r) hF,
          finsum_mem_coe_finset]
      _ ≤ (reachBall Γ o (5*r)).ncard := Set.ncard_le_ncard hsub (reachBall_finite Γ hl o _)
  have hpos : 0<(reachBall Γ o r).ncard :=
    (Set.ncard_pos (reachBall_finite Γ hl o r)).mpr ⟨o,reachBall_self Γ o r⟩
  refine ⟨F,hFo,le_of_mul_le_mul_right (hcount.trans hd) hpos,?_⟩
  intro u hu
  by_cases huF : u∈F
  · exact ⟨u,huF,reachBall_self Γ u _⟩
  by_cases! H : ∀ v∈F, Disjoint (reachBall Γ u r) (reachBall Γ v r)
  · refine False.elim (hFmax.not_gt ?_ (Finset.ssubset_insert huF))
    rw [Finset.insert_subset_iff,Finset.coe_insert]
    exact ⟨⟨(reachBall_finite Γ hl o (4*r)).mem_toFinset.mpr hu,hFA⟩,
      hF.insert (fun v hv _ => H v hv)⟩
  · simp_rw [Set.not_disjoint_iff] at H
    obtain ⟨v,hv,w,hwu,hwv⟩ := H
    refine ⟨v,hv,?_⟩
    simpa only [show r+r=2*r by omega] using
      reachBall_add Γ hwv (reachBall_symm Γ hwu)

lemma displacement_cover_of_doubling (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    CovBySMul (Γ ≃g Γ) (K : ℝ) (displacement Γ o (4*r)) (displacement Γ o (2*r)) := by
  obtain ⟨F,hFo,hFK,hcover⟩ := reachBall_packing Γ hl ht o r K hd
  have hex : ∀ v : F, ∃ φ : Γ ≃g Γ, φ o=v.val := fun v => ht o v.val
  choose φ hφ using hex
  let H := Finset.univ.image φ
  have hH : H.card≤K := (Finset.card_image_le).trans (by simpa using hFK)
  refine ⟨H,by exact_mod_cast hH,?_⟩
  intro ψ hψ
  obtain ⟨v,hv,huv⟩ := hcover (ψ o) hψ
  let c := φ ⟨v,hv⟩
  have hc : c∈H := Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hco : c o=v := hφ ⟨v,hv⟩
  have hrem : c⁻¹*ψ∈displacement Γ o (2*r) := by
    have hh := iso_reachBall Γ c.symm huv
    rw [←hco] at hh
    change c.symm (ψ o)∈reachBall Γ o (2*r)
    simpa using hh
  change ψ∈(H : Set (Γ ≃g Γ))*displacement Γ o (2*r)
  exact Set.mem_mul.mpr ⟨c,hc,c⁻¹*ψ,hrem,by simp⟩

lemma displacement_approximate_of_doubling (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (r K : ℕ)
    (hd : (reachBall Γ o (5*r)).ncard≤K*(reachBall Γ o r).ncard) :
    IsApproximateSubgroup (K : ℝ) (displacement Γ o (2*r)) where
  one_mem := one_mem_displacement Γ o _
  inv_eq_self := by
    ext φ
    change φ⁻¹∈displacement Γ o (2*r) ↔ φ∈displacement Γ o (2*r)
    exact displacement_inv Γ
  sq_covBySMul := by
    apply (displacement_cover_of_doubling Γ hl ht o r K hd).subset_left
    rw [pow_two]
    simpa only [show 2*r+2*r=4*r by omega] using displacement_mul_subset Γ o (2*r) (2*r)

theorem compact_open_approximate_scales
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d) :
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∀ R : ℕ, ∃ n≥R, IsCompact (displacement Γ o (2*n)) ∧
      IsOpen (displacement Γ o (2*n)) ∧
      IsApproximateSubgroup (5^(d+1) : ℝ) (displacement Γ o (2*n)) := by
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  dsimp only
  intro R
  obtain ⟨n,hn,hd⟩ := sparse_polynomial_doubling_scales
    (fun n => (reachBall Γ o n).ncard)
    (fun r s hrs => Set.ncard_le_ncard (reachBall_mono Γ o hrs) (reachBall_finite Γ hl o s))
    (fun n => (Set.ncard_pos (reachBall_finite Γ hl o n)).mpr ⟨o,reachBall_self Γ o n⟩)
    d hpoly R
  refine ⟨n,hn,compact_displacement Γ hc hl o _,open_displacement Γ o _,?_⟩
  exact_mod_cast displacement_approximate_of_doubling Γ hl ht o n (5^(d+1)) hd

end CriticalPercolation.GraphTopology
end
end

end OAI

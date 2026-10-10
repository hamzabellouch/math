import OAI.Geometry.LatticeCovering.Completion

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal




theorem quotient_hole_bound {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (ε : ℝ≥0∞)
    (hhole : ∀ y, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤ ε) :
    torusMeasure (m+D) ((joinedProjection L N M Z '' K)ᶜ) ≤ ε := by
  let π := joinedProjection L N M Z
  have hC : MeasurableSet ((π '' K)ᶜ) := (hK.image π.continuous).measurableSet.compl
  rw [←(appendTorus_measurePreserving m D).measure_preimage hC.nullMeasurableSet]
  have hpre : MeasurableSet ((appendTorus m D) ⁻¹' (π '' K)ᶜ) :=
    (appendTorus m D).continuous.measurable hC
  rw [Measure.prod_apply_symm hpre]
  calc
    (∫⁻ v : Torus D, torusMeasure m ((fun t => (t,v)) ⁻¹'
        ((appendTorus m D) ⁻¹' (π '' K)ᶜ)) ∂(torusMeasure D)) ≤
        (∫⁻ _v : Torus D, ε ∂(torusMeasure D)) := by
      apply lintegral_mono
      intro v
      obtain ⟨z,hz⟩ := latticeProjection_surjective N v
      have hsub : (fun t => (t,v)) ⁻¹' ((appendTorus m D) ⁻¹' (π '' K)ᶜ) ⊆
          (fun t => t+latticeProjection L (columnMap Z z)) ⁻¹'
            horizontalHole L K (joinedLattice L N M Z) (M z) := by
        intro t ht
        obtain ⟨x,hx⟩ := latticeProjection_surjective L (t+latticeProjection L (columnMap Z z))
        have hπ : π (Fin.append x (M z)) = appendTorus m D (t,v) := by
          simp only [π,joinedProjection_append,map_sub,hx,hz,add_sub_cancel_right]
          rfl
        have hnot : Fin.append x (M z) ∉ K+(joinedLattice L N M Z : Set (Fin (m+D) → ℝ)) := by
          intro hc
          have hm := (projection_mem_image_iff (joinedLattice L N M Z) π.toAddMonoidHom
            (joinedProjection_eq_zero_iff L N M Z) K (Fin.append x (M z))).mpr hc
          change π (Fin.append x (M z)) ∈ π '' K at hm
          rw [hπ] at hm
          exact ht hm
        exact ⟨x,hnot,hx⟩
      apply le_trans (measure_mono hsub)
      rw [measure_preimage_add_right]
      exact hhole (M z)
    _ = ε := by simp

lemma quotient_real_hole_bound {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (ε : ℝ) (hε : 0 ≤ ε)
    (hhole : ∀ y, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤ ENNReal.ofReal ε) :
    1-(torusMeasure (m+D)).real (joinedProjection L N M Z '' K) ≤ ε := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (quotient_hole_bound L N M Z K hK (ENNReal.ofReal ε) hhole)
  rw [ENNReal.toReal_ofReal hε] at h
  have he := measureReal_compl (μ := torusMeasure (m+D))
    (hK.image (joinedProjection L N M Z).continuous).measurableSet
  simpa using he.symm.trans_le h



theorem joined_holes_to_cover {m D : ℕ} (hn : 2 ≤ m+D)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hhole : ∀ y, torusMeasure m (horizontalHole L K (joinedLattice L N M Z) y) ≤
      ENNReal.ofReal (1/((m+D : ℕ) : ℝ)^(2*(m+D)))) :
    ∃ (Λ : Submodule ℤ (Fin (m+D) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+D) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ ≤
        Real.exp 1*((volume K).toReal /
          (ZLattice.covolume L*ZLattice.covolume (image N M))) := by
  have hh := quotient_real_hole_bound L N M Z K hK
    (1/((m+D : ℕ) : ℝ)^(2*(m+D))) (by positivity) hhole
  obtain ⟨Λ,hd,hfull,hcover,hdensity⟩ := complete_almost_cover_projection hn
    (joinedLattice L N M Z) (joinedProjection L N M Z)
    (joinedProjection_surjective L N M Z) (joinedProjection_eq_zero_iff L N M Z)
    K hK hconv hh
  exact ⟨Λ,hd,hfull,hcover,by simpa only [joined_covolume] using hdensity⟩



end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion Shear
open scoped BigOperators Pointwise ENNReal




theorem finite_patterns_to_cover {α : Type*} [Fintype α] {m D : ℕ} (hn : 2 ≤ m+D)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (hints : ∀ k : Fin D → ℤ, (fun j => (k j : ℝ)) ∈ N)
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (K : Set (Fin (m+D) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (J : α → Set (Fin m → ℝ)) (hJ : ∀ a, IsCompact (J a))
    (u : α → ℝ) (labels : Finset α)
    (hhole : ∀ a ∈ labels, torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-u a/2)))
    (alphabet : ℕ → Finset ℝ) (Lstar A : ℝ) (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (D+1),
      (allPatterns alphabet labels q).card : ℕ) : ℝ) < Lstar)
    (herror : Real.exp ((2^D : ℕ)*Real.log Lstar-A/2) ≤ 1/((m+D : ℕ) : ℝ)^(2*(m+D)))
    (hpatterns : ∀ z : Fin D → ℝ, (∀ j, 0 ≤ z j ∧ z j < 1) →
      ∃ s : Finset ((Fin D → ℝ) × α), s ∈ allPatterns alphabet labels D ∧
        (∀ l ∈ s, l.1 ∈ N) ∧
        (∀ l ∈ s, ∀ j ∈ J l.2, Fin.append j (M z-M l.1) ∈ K) ∧
        A ≤ ∑ l ∈ s, u l.2) :
    ∃ (Λ : Submodule ℤ (Fin (m+D) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+D) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ ≤
        Real.exp 1*((volume K).toReal /
          (ZLattice.covolume L*ZLattice.covolume (image N M))) := by
  obtain ⟨Z,hZ⟩ := finite_family_lattice_shear L N M K J hJ u labels hhole alphabet Lstar hLstar hcost
  apply joined_holes_to_cover hn L N M Z K hK hconv
  apply all_height_hole_bound L N hints M Z K
  intro z hz
  obtain ⟨s,hs,hraw,hsection,hload⟩ := hpatterns z hz
  exact (hZ (M z) s hs hraw hsection A hload).trans (ENNReal.ofReal_le_ofReal herror)


end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.Vertical
open ConstructionA LatticeGeometry

lemma Block.integer_mem (B : Block) (k : Fin B.b → ℤ) :
    (fun j => (k j : ℝ)) ∈ B.lattice := by
  change ∃ z : Fin B.b → ℤ, residue B.p z ∈ Submodule.span (ZMod B.p) {B.direction} ∧
    (fun j => (z j : ℝ)/(B.p : ℝ)) = (fun j => (k j : ℝ))
  refine ⟨fun j => B.p*k j,?_,?_⟩
  · convert (Submodule.span (ZMod B.p) {B.direction}).zero_mem using 1
    ext j
    simp [residue]
  · ext j
    push_cast
    field_simp [B.prime.ne_zero]

namespace Chain
variable {B : Block}
lemma raw_integer_mem (c : Chain B) (k : Fin c.dim → ℤ) :
    (fun j => (k j : ℝ)) ∈ c.rawLattice := by
  induction c with
  | base B => exact B.integer_mem k
  | append c B w ih =>
    exact ⟨ih (fun j => k (Fin.castAdd B.b j)),
      B.integer_mem (fun j => k (Fin.natAdd c.dim j))⟩

lemma full_raw_integer_mem (c : Chain B) (k : Fin c.fullDim → ℤ) :
    (fun j => (k j : ℝ)) ∈ c.fullRaw :=
  ⟨c.raw_integer_mem (fun j => k (Fin.castAdd B.terminalDim j)),
    integer_mem _ (fun j => k (Fin.natAdd c.dim j))⟩

noncomputable def alphabetSeq (c : Chain B) (j : ℕ) : Finset ℝ :=
  if h : j<c.fullDim then c.alphabets ⟨j,h⟩ else ∅

@[simp] lemma alphabetSeq_fin (c : Chain B) (j : Fin c.fullDim) :
    c.alphabetSeq j.val=c.alphabets j := by
  simp [alphabetSeq,j.isLt]
end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry
open scoped BigOperators Pointwise ENNReal





theorem prepared_chain_to_cover {α : Type*} [Fintype α] {B : Block} (c : Chain B)
    {m : ℕ} (hn : 2 ≤ m+c.fullDim)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (J : α → Set (Fin m → ℝ)) (hJ : ∀ a, IsCompact (J a)) (u : α → ℝ)
    (κ ρ csec Csec ε τ A Lstar : ℝ)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ csec) (hC : 0 ≤ Csec) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
        c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hsection : ∀ v : c.FullVec, (∑ j, (v j)^2) ≤ c.radiusSq+(B.terminalDim : ℝ) →
      ∃ a : α, (∀ j ∈ J a, Fin.append j v ∈ K) ∧
        csec*ρ*(c.det*gamma v) ≤ u a ∧ u a ≤ Csec*ρ*(c.det*gamma v))
    (hhole : ∀ a, τ ≤ u a → u a ≤ Csec*ρ*ε →
      torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤ ENNReal.ofReal (Real.exp (-u a/2)))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ csec*κ*ρ)
    (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (c.fullDim+1),
      (allPatterns c.alphabetSeq
        (Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ Csec*ρ*ε)) q).card : ℕ) : ℝ) < Lstar)
    (herror : Real.exp ((2^c.fullDim : ℕ)*Real.log Lstar-A/2) ≤
      1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ ≤
        Real.exp 1*((volume K).toReal /(ZLattice.covolume L*c.det)) := by
  classical
  let labels := Finset.univ.filter (fun a => τ ≤ u a ∧ u a ≤ Csec*ρ*ε)
  have hs : ∀ a ∈ labels, torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-u a/2)) := by
    intro a ha
    exact hhole a (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
  obtain ⟨Λ,hd,hfull,hcover,hdens⟩ := finite_patterns_to_cover hn L c.fullRaw
    c.full_raw_integer_mem c.fullLinear K hK hconv J hJ u labels hs
    c.alphabetSeq Lstar A hLstar hcost herror (by
      intro z hz
      obtain ⟨P,hPn,hPb,hPl,hPw⟩ := hpat (c.fullLinear z)
      exact section_labeled_retained P hPn hPb c.fullRaw (fun l hl => (hPl l hl).1)
        c.fullLinear (c.fullLinear z) K J u (fun l => c.det*gamma (c.fullLinear z-c.fullLinear l))
        κ ρ csec Csec ε τ A hρ hc hC hτ hA hPw (fun l hl => (hPl l hl).2.2)
        (fun l hl => hsection _ (c.full_residual_square _ _ (hPl l hl).2.1))
        hload c.alphabetSeq (by
          intro l hl j
          rw [Chain.alphabetSeq_fin]
          exact c.mem_alphabets z l hz (hPl l hl).2.1 (hPl l hl).1 j))
  refine ⟨Λ,hd,hfull,hcover,?_⟩
  change (volume K).toReal / ZLattice.covolume Λ ≤
    Real.exp 1*((volume K).toReal /(ZLattice.covolume L*ZLattice.covolume c.fullLattice)) at hdens
  simpa only [c.full_covolume] using hdens


end SingleLatticeCovering.Vertical

end
end

section

noncomputable section
namespace SingleLatticeCovering.Vertical
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry
open scoped BigOperators Pointwise ENNReal

lemma Chain.det_pos {B : Block} (c : Chain B) : 0 < c.det := by
  rw [←c.full_covolume]
  exact ZLattice.covolume_pos c.fullLattice




theorem labeled_chain_to_cover {α : Type*} [Fintype α] {B : Block} (c : Chain B)
    {m : ℕ} (hn : 2 ≤ m+c.fullDim)
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (Fin (m+c.fullDim) → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal)
    (J : α → Set (Fin m → ℝ)) (hJ : ∀ a, IsCompact (J a))
    (κ ρ csec Csec ε τ A Lstar : ℝ)
    (hρ : 0 < ρ) (hc : 0 ≤ csec) (hC : 0 ≤ Csec) (hτ : 0 ≤ τ) (hA : 0 < A)
    (hcov : ZLattice.covolume L volume=(volume K).toReal/(ρ*c.det))
    (hpat : ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
      P.Nonempty ∧ SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
        c.det*gamma (y-c.fullLinear l) ≤ ε) ∧
      κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l))
    (hsection : ∀ v : c.FullVec, (∑ j, (v j)^2) ≤ c.radiusSq+(B.terminalDim : ℝ) →
      ∃ a : α, (∀ j ∈ J a, Fin.append j v ∈ K) ∧
        csec*(volume K).toReal*gamma v ≤ (volume (J a)).toReal ∧
        (volume (J a)).toReal ≤ Csec*(volume K).toReal*gamma v)
    (hhole : ∀ a, τ ≤ (volume (J a)).toReal/ZLattice.covolume L volume →
      (volume (J a)).toReal/ZLattice.covolume L volume ≤ Csec*ρ*ε →
      torusMeasure m ((latticeProjection L '' J a)ᶜ) ≤
        ENNReal.ofReal (Real.exp (-((volume (J a)).toReal/ZLattice.covolume L volume)/2)))
    (hload : A+(2^c.fullDim : ℕ)*τ ≤ csec*κ*ρ)
    (hLstar : 1 ≤ Lstar)
    (hcost : ((∑ q ∈ Finset.range (c.fullDim+1),
      (allPatterns c.alphabetSeq
        (Finset.univ.filter (fun a => τ ≤ (volume (J a)).toReal/ZLattice.covolume L volume ∧
          (volume (J a)).toReal/ZLattice.covolume L volume ≤ Csec*ρ*ε)) q).card : ℕ) : ℝ) < Lstar)
    (herror : Real.exp ((2^c.fullDim : ℕ)*Real.log Lstar-A/2) ≤
      1/((m+c.fullDim : ℕ) : ℝ)^(2*(m+c.fullDim))) :
    ∃ (Λ : Submodule ℤ (Fin (m+c.fullDim) → ℝ)) (_ : DiscreteTopology Λ),
      IsZLattice ℝ Λ ∧ K+(Λ : Set (Fin (m+c.fullDim) → ℝ)) = Set.univ ∧
      (volume K).toReal / ZLattice.covolume Λ volume ≤ Real.exp 1*ρ := by
  have _ := hV
  have hL : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos L
  have hVeq : (volume K).toReal=ZLattice.covolume L volume*(ρ*c.det) := by
    rw [hcov]; exact (div_mul_cancel₀ _ (mul_pos hρ c.det_pos).ne').symm
  have hratio (a g : ℝ) : (a*(volume K).toReal*g)/ZLattice.covolume L volume=a*ρ*(c.det*g) := by
    rw [hVeq]
    field_simp [hL.ne']
  obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := prepared_chain_to_cover c hn L K hK hconv J hJ
    (fun a => (volume (J a)).toReal/ZLattice.covolume L volume) κ ρ csec Csec ε τ A Lstar
    hρ.le hc hC hτ hA hpat (by
      intro v hv
      obtain ⟨a,ha,hl,hu⟩ := hsection v hv
      refine ⟨a,ha,?_,?_⟩
      · rw [←hratio csec (gamma v)]
        exact div_le_div_of_nonneg_right hl hL.le
      · rw [←hratio Csec (gamma v)]
        exact div_le_div_of_nonneg_right hu hL.le) hhole hload hLstar hcost herror
  refine ⟨Λ,hd,hfull,hcover,?_⟩
  have heq : (volume K).toReal/(ZLattice.covolume L volume*c.det)=ρ := by
    rw [hVeq]
    field_simp [hL.ne',c.det_pos.ne']
  simpa only [heq] using hbound


end SingleLatticeCovering.Vertical

end
end

section

namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affine_image_volume {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (t : Fin n → ℝ) (K : Set (Fin n → ℝ)) :
    volume ((fun x => e x+t) '' K) = ENNReal.ofReal |LinearMap.det e.toLinearMap| * volume K := by
  have hs : (fun x => e x+t) '' K = (fun x => x+t) '' (e '' K) := by
    rw [Set.image_image]
  rw [hs,Set.image_add_right,measure_preimage_add_right]
  exact volume.addHaar_image_linearMap e.toLinearMap K

lemma affine_image_cover {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hcover : K+(L : Set (Fin n → ℝ))=Set.univ) :
    (fun x => e x+t) '' K+(image L e : Set (Fin n → ℝ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : e.symm (x-t) ∈ K+(L : Set (Fin n → ℝ)) := by rw [hcover]; trivial
  obtain ⟨k,hk,l,hl,hkl⟩ := hx
  refine ⟨e k+t,⟨k,hk,rfl⟩,e l,(mem_image L e (e l)).mpr ⟨l,hl,rfl⟩,?_⟩
  change e k+t+e l=x
  have he : e k+e l=x-t := by
    rw [←map_add]
    change k+l=e.symm (x-t) at hkl
    rw [hkl,e.apply_symm_apply]
  calc e k+t+e l = (e k+e l)+t := by abel
       _ = x := by rw [he]; abel

lemma affine_image_density {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) :
    (volume ((fun x => e x+t) '' K)).toReal / ZLattice.covolume (image L e) =
      (volume K).toReal / ZLattice.covolume L := by
  rw [affine_image_volume,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),image_covolume]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr e.isUnit_det'.ne_zero)


end SingleLatticeCovering.LatticeGeometry

noncomputable section
namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affineEquiv_eq_linear_add {n : ℕ}
    (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) : e x=e.linear x+e 0 := by
  have h := e.map_vadd (0 : Fin n → ℝ) x
  simpa using h



lemma pull_back_cover {n : ℕ} (e : (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hcover : e '' K+(L : Set (Fin n → ℝ))=Set.univ) {d : ℝ}
    (hd : (volume (e '' K)).toReal/ZLattice.covolume L ≤ d) :
    ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
      K+(Λ : Set (Fin n → ℝ))=Set.univ ∧ (volume K).toReal/ZLattice.covolume Λ ≤ d := by
  let Λ := image L e.symm.linear
  have he : (fun x => e.symm.linear x+e.symm 0) '' (e '' K)=K := by
    simp_rw [←affineEquiv_eq_linear_add]
    exact e.symm_image_image K
  refine ⟨Λ,inferInstance,inferInstance,?_,?_⟩
  · have h := affine_image_cover L e.symm.linear (e.symm 0) (e '' K) hcover
    rwa [he] at h
  · have h := affine_image_density L e.symm.linear (e.symm 0) (e '' K)
    rw [he] at h
    exact h.trans_le hd


end SingleLatticeCovering.LatticeGeometry

end
end

section


noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

lemma compact_separated_cover {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (hK : IsCompact K) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ S : Finset E, (↑S : Set E) ⊆ K ∧
      Metric.IsSeparated δ (↑S : Set E) ∧ Metric.IsCover δ K (↑S : Set E) := by
  classical
  obtain ⟨U,hUK,hUf,hUC⟩ := Metric.exists_finite_isCover_of_isCompact
    (ε := δ/2) (by positivity) hK
  have hfin : Metric.packingNumber δ K ≠ ⊤ := by
    have hh := Metric.packingNumber_two_mul_le_externalCoveringNumber (δ/2) K
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] at hh
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hUf) (hh.trans hUC.externalCoveringNumber_le_encard)
  have hSf' : (Metric.maximalSeparatedSet δ K).Finite :=
    Set.encard_ne_top_iff.mp (by rw [Metric.encard_maximalSeparatedSet hfin]; exact hfin)
  exact ⟨hSf'.toFinset,by simpa using (Metric.maximalSeparatedSet_subset (ε := δ) (A := K)),
    by simpa using (Metric.isSeparated_maximalSeparatedSet (ε := δ) (A := K)),
    by simpa using Metric.isCover_maximalSeparatedSet hfin⟩



lemma separated_card_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (S : Finset E) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hS : ∀ x ∈ S, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < dist x y) :
    (S.card : ℝ) ≤ (1+2*R/δ)^(finrank ℝ E) := by
  classical
  have hd : 0 < δ/2 := half_pos hδ
  have hdis : (↑S : Set E).PairwiseDisjoint (fun x => Metric.ball x (δ/2)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hxz : dist x z < δ/2 := by simpa only [Metric.mem_ball,dist_comm] using hzx
    have hzy' : dist z y < δ/2 := hzy
    have hh := dist_triangle x z y
    have hxy' := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ (↑S : Set E), Metric.ball x (δ/2)) ⊆ Metric.ball (0 : E) (R+δ/2) := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := Set.mem_iUnion₂.mp hz
    rw [Metric.mem_ball,dist_zero_right]
    have hdist : dist z x < δ/2 := hzx
    have hh := norm_add_le (z-x) x
    rw [sub_add_cancel,←dist_eq_norm] at hh
    linarith [hS x hx]
  have hμ := measure_mono (μ := μ) hsub
  simp only [Finset.mem_coe] at hμ
  rw [measure_biUnion_finset hdis (fun x hx => Metric.isOpen_ball.measurableSet)] at hμ
  simp_rw [μ.addHaar_ball_of_pos _ hd] at hμ
  rw [Finset.sum_const, nsmul_eq_mul,
    μ.addHaar_ball_of_pos _ (by linarith : 0 < R+δ/2)] at hμ
  have hunit0 : μ (Metric.ball (0 : E) 1) ≠ 0 :=
    Metric.isOpen_ball.measure_ne_zero μ ⟨0, by simp⟩
  have hunitTop : μ (Metric.ball (0 : E) 1) ≠ ∞ :=
    measure_ball_ne_top
  have hreal : (S.card : ℝ)*(δ/2)^finrank ℝ E ≤ (R+δ/2)^finrank ℝ E := by
    have hh := (ENNReal.mul_le_mul_iff_left hunit0 hunitTop).mp (by simpa only [←mul_assoc] using hμ)
    have hs : (S.card : ℝ≥0∞)*ENNReal.ofReal ((δ/2)^finrank ℝ E) =
        ENNReal.ofReal ((S.card : ℝ)*(δ/2)^finrank ℝ E) := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]; simp
    rw [hs] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have he : (1+2*R/δ)^finrank ℝ E = (R+δ/2)^finrank ℝ E/(δ/2)^finrank ℝ E := by
    rw [←div_pow]; congr 1; field_simp; ring
  rw [he]
  exact (le_div_iff₀ (pow_pos hd _)).mpr hreal


lemma ball_finite_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] {R : ℝ} (hR : 0 < R)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ S : Finset E, (S.card : ℝ) ≤ (3*(m : ℝ)^2)^(finrank ℝ E) ∧
      (∀ a ∈ S, ‖a‖ ≤ R) ∧
      ∀ y : E, ‖y‖ ≤ R → ∃ a ∈ S, dist y a ≤ R/(m : ℝ)^2 := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < R/(m : ℝ)^2 := div_pos hR (pow_pos hm0 2)
  let δ : ℝ≥0 := ⟨R/(m : ℝ)^2,hd.le⟩
  obtain ⟨S,hS,hsep,hcover⟩ := compact_separated_cover (Metric.closedBall (0 : E) R)
    (isCompact_closedBall _ _) (show 0 < δ from hd)
  have hSn : ∀ a ∈ S, ‖a‖ ≤ R := by
    intro a ha
    simpa only [Metric.mem_closedBall,dist_zero_right] using hS ha
  have hsep' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → R/(m : ℝ)^2 < dist x y := by
    intro x hx y hy hxy
    have hh := ENNReal.toReal_strict_mono (edist_ne_top x y) (hsep hx hy hxy)
    rw [ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] at hh
    exact hh
  have hcard := separated_card_bound μ S hR.le hd hSn hsep'
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio : 1+2*R/(R/(m : ℝ)^2) ≤ 3*(m : ℝ)^2 := by
    have he : 2*R/(R/(m : ℝ)^2)=2*(m : ℝ)^2 := by field_simp
    rw [he]; nlinarith
  refine ⟨S,hcard.trans (pow_le_pow_left₀ (by positivity) hratio _),hSn,?_⟩
  intro y hy
  obtain ⟨a,ha,hya⟩ := hcover (show y ∈ Metric.closedBall (0 : E) R by simpa using hy)
  refine ⟨a,ha,?_⟩
  have hh := ENNReal.toReal_mono ENNReal.coe_ne_top hya
  rw [ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] at hh
  exact hh




end SingleLatticeCovering.Sections




noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fiber (K : Set (E × F)) (y : F) : Set E := {x | (x,y) ∈ K}

lemma fiber_compact {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K) (y : F) :
    IsCompact (fiber K y) := by
  have he : fiber K y = Prod.fst '' (K ∩ Prod.snd ⁻¹' {y}) := by
    ext x; constructor
    · intro hx; exact ⟨(x,y),⟨hx,by simp⟩,rfl⟩
    · rintro ⟨⟨x',y'⟩,⟨hxy,hy⟩,hx⟩
      have hy' : y'=y := hy
      change x'=x at hx
      subst x'; subst y'; exact hxy
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

lemma fiber_convex {K : Set (E × F)} (hK : Convex ℝ K) (y : F) :
    Convex ℝ (fiber K y) := by
  intro x hx z hz a b ha hb hab
  have hh := hK hx hz ha hb hab
  simpa only [fiber, Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk,
    ←add_smul,hab,one_smul] using hh



lemma nearby_fiber_inclusion {K : Set (E × F)} (hK : Convex ℝ K)
    {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 1 ≤ m)
    (hcenter : ∀ z : F, ‖z‖ ≤ 2*R → (0,z) ∈ K)
    {a y : F} (ha : ‖a‖ ≤ R) (hya : dist y a ≤ R/(m : ℝ)^2) :
    (1-(m : ℝ)^(-2 : ℤ)) • fiber K a ⊆ fiber K y := by
  have _ := hR
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  let z := a+(m : ℝ)^2 • (y-a)
  have hz : ‖z‖ ≤ 2*R := by
    calc
      _ ≤ ‖a‖+‖(m : ℝ)^2 • (y-a)‖ := norm_add_le _ _
      _ = ‖a‖+(m : ℝ)^2*dist y a := by rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _),dist_eq_norm]
      _ ≤ R+(m : ℝ)^2*(R/(m : ℝ)^2) := add_le_add ha (mul_le_mul_of_nonneg_left hya (sq_nonneg _))
      _ = 2*R := by field_simp; ring
  have ht : 0 ≤ 1-(m : ℝ)^(-2 : ℤ) := by
    norm_num only [zpow_neg, zpow_ofNat]
    have hh : 1 ≤ (m : ℝ)^2 := one_le_pow₀ hm1
    exact sub_nonneg.mpr ((inv_le_one₀ (pow_pos hm0 _)).mpr hh)
  intro v hv
  obtain ⟨x,hx,rfl⟩ := hv
  have hh := hK hx (hcenter z hz) ht (by positivity : 0 ≤ (m : ℝ)^(-2 : ℤ)) (by ring)
  have he : (1-(m : ℝ)^(-2 : ℤ)) • a+(m : ℝ)^(-2 : ℤ) • z=y := by
    dsimp [z]; rw [smul_add,smul_smul]
    norm_num only [zpow_neg, zpow_ofNat]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hm0.ne'),one_smul]
    module
  simpa only [fiber,Set.mem_ofPred_eq,Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero,he] using hh

lemma shrink_power_half {m : ℕ} (hm : 2 ≤ m) :
    (1-(m : ℝ)^(-2 : ℤ))^m ≥ (1/2 : ℝ) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (m : ℝ)^2 := by positivity
  have hinv : (m : ℝ)^(-2 : ℤ)=((m : ℝ)^2)⁻¹ := by norm_num [zpow_neg]
  rw [hinv]
  have hi : ((m : ℝ)^2)⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr (by nlinarith)
  have hh := one_add_mul_le_pow (show -2 ≤ -((m : ℝ)^2)⁻¹ by linarith) m
  have he : (m : ℝ)*((m : ℝ)^2)⁻¹=(m : ℝ)⁻¹ := by field_simp
  have hi2 : (m : ℝ)⁻¹ ≤ 1/2 := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hm2
  simp only [mul_neg,he,←sub_eq_add_neg] at hh
  linarith



lemma prescribed_volume [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (hn : 0 < finrank ℝ E)
    {A : Set E} (hA : IsCompact A) (hconv : Convex ℝ A) (hzero : (0 : E) ∈ A)
    {v : ℝ} (hv : 0 < v) (hvol : v ≤ (μ A).toReal) :
    ∃ J : Set E, IsCompact J ∧ Convex ℝ J ∧ (0 : E) ∈ J ∧ J ⊆ A ∧ (μ J).toReal=v := by
  have hμ : 0 < (μ A).toReal := hv.trans_le hvol
  let t : ℝ := (v/(μ A).toReal)^((finrank ℝ E : ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hv hμ) _
  have ht1 : t ≤ 1 := Real.rpow_le_one (by positivity) ((div_le_one hμ).mpr hvol) (by positivity)
  refine ⟨t • A, hA.smul t, hconv.smul t,?_,?_,?_⟩
  · exact ⟨0,hzero,smul_zero _⟩
  · rintro x ⟨a,ha,rfl⟩
    exact hconv.smul_mem_of_zero_mem hzero ha ⟨ht.le,ht1⟩
  · rw [μ.addHaar_smul_of_nonneg ht.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht.le _)]
    have he : t^finrank ℝ E=v/(μ A).toReal :=
      Real.rpow_inv_natCast_pow (div_pos hv hμ).le hn.ne'
    rw [he,div_mul_cancel₀ _ hμ.ne']




end SingleLatticeCovering.Sections





noncomputable section

end
end
end
end
end

end OAI

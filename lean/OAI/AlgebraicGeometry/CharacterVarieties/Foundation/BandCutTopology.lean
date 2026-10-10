import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BandIncidence

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence PortAssembly
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)

abbrev bandCutParent : F := D.ports.facet ⟨q,none⟩

def bandCutExtra (f : F) : ℕ := if f=D.bandCutParent q then 1 else 0

def bandCutBoundaryCount (f : F) : ℕ := D.boundaryCount f + D.bandCutExtra q f

def bandCutBoundaryLength (f : F) (b : Fin (D.bandCutBoundaryCount q f)) : ℕ :=
  Sum.elim (fun b => D.boundaryLength f b * 3) (fun _ => 2)
    ((finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).symm b)

lemma bandCutExtra_eq (f : F) (j : Fin (D.bandCutExtra q f)) : f=D.bandCutParent q := by
  by_contra h
  have := j.isLt
  simp [bandCutExtra,h] at this

/-- There is exactly one additional boundary, at the selected parent facet. -/
def bandCutExtraPositions :
    ((f : F) × (_ : Fin (D.bandCutExtra q f)) × Fin 2) ≃ Fin 2 where
  toFun x := x.2.2
  invFun k := ⟨D.bandCutParent q,⟨0,by simp [bandCutExtra]⟩,k⟩
  left_inv := by
    rintro ⟨f,j,k⟩
    have h := D.bandCutExtra_eq q f j
    subst f
    have hj : j=⟨0,by simp [bandCutExtra]⟩ := by
      apply Fin.ext
      change j.val = 0
      have hjlt : j.val < 1 := by simpa [bandCutExtra] using j.isLt
      omega
    subst j
    rfl
  right_inv _ := rfl

/-- Divide each old boundary index into its old side and its phase. -/
def bandCutTriplePositions :
    ((f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b*3)) ≃
      ((f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b)) × Fin 3 where
  toFun x := (⟨x.1,x.2.1,x.2.2.divNat⟩,x.2.2.modNat)
  invFun x := ⟨x.1.1,x.1.2.1,finProdFinEquiv (x.1.2.2,x.2)⟩
  left_inv := by
    rintro ⟨f,b,i⟩
    exact congrArg (fun j => (⟨f,b,j⟩ :
      ((f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b*3))))
      (finProdFinEquiv.apply_symm_apply i)
  right_inv := by
    rintro ⟨⟨f,b,i⟩,j⟩
    exact congrArg (fun p : Fin (D.boundaryLength f b) × Fin 3 =>
      ((⟨f,b,p.1⟩ : ((f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b))),p.2))
      (finProdFinEquiv.symm_apply_apply (i,j))

def bandCutBoundaryPositions :
    ((f : F) × (b : Fin (D.bandCutBoundaryCount q f)) × Fin (D.bandCutBoundaryLength q f b)) ≃
      (Side S arity × Fin 3) ⊕ Fin 2 :=
  (Equiv.sigmaCongrRight (fun f => (Equiv.sigmaCongrLeft
    (finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).symm).trans
      (Equiv.sumSigmaDistrib (fun x => Fin (Sum.elim
        (fun b => D.boundaryLength f b*3) (fun _ => 2) x))))).trans
    ((Equiv.sigmaSumDistrib _ _).trans
      (Equiv.sumCongr (D.bandCutTriplePositions.trans (Equiv.prodCongr D.boundarySide (Equiv.refl _)))
        (D.bandCutExtraPositions q)))

def bandCutBoundarySide :
    ((f : F) × (b : Fin (D.bandCutBoundaryCount q f)) × Fin (D.bandCutBoundaryLength q f b)) ≃
      Side (BandCutSeam S) (bandCutArity arity) :=
  (D.bandCutBoundaryPositions q).trans (bandCutSideEquiv q)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence PortAssembly
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)

@[simp] lemma bandCutBoundaryLength_old (f : F) (b : Fin (D.boundaryCount f)) :
    D.bandCutBoundaryLength q f (finSumFinEquiv (.inl b)) = D.boundaryLength f b*3 := by
  simp [bandCutBoundaryLength]

@[simp] lemma bandCutBoundaryLength_new (f : F) (j : Fin (D.bandCutExtra q f)) :
    D.bandCutBoundaryLength q f (finSumFinEquiv (.inr j)) = 2 := by
  simp [bandCutBoundaryLength]

lemma bandCutBoundarySide_old (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b*3)) :
    D.bandCutBoundarySide q ⟨f,finSumFinEquiv (.inl b),
      Fin.cast (D.bandCutBoundaryLength_old q f b).symm i⟩ =
      bandCutLong q (D.boundarySide ⟨f,b,i.divNat⟩,i.modNat) := by
  have he : (⟨(finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).symm
      (finSumFinEquiv (.inl b)), Fin.cast (D.bandCutBoundaryLength_old q f b).symm i⟩ :
      (x : Fin (D.boundaryCount f) ⊕ Fin (D.bandCutExtra q f)) ×
        Fin (Sum.elim (fun b => D.boundaryLength f b*3) (fun _ => 2) x)) = ⟨.inl b,i⟩ := by
    refine Sigma.ext (Equiv.symm_apply_apply _ _) ?_
    exact (Fin.heq_ext_iff (D.bandCutBoundaryLength_old q f b)).mpr rfl
  exact congrArg (fun z => (bandCutSideEquiv q)
    ((Equiv.sumCongr (D.bandCutTriplePositions.trans
      (Equiv.prodCongr D.boundarySide (Equiv.refl _))) (D.bandCutExtraPositions q))
        ((Equiv.sigmaSumDistrib _ _) ⟨f,(Equiv.sumSigmaDistrib (fun x =>
          Fin (Sum.elim (fun b => D.boundaryLength f b*3) (fun _ => 2) x))) z⟩))) he


lemma bandCutBoundarySide_new (f : F) (j : Fin (D.bandCutExtra q f)) (i : Fin 2) :
    D.bandCutBoundarySide q ⟨f,finSumFinEquiv (.inr j),
      Fin.cast (D.bandCutBoundaryLength_new q f j).symm i⟩ =
      bandCutShort q i := by
  have he : (⟨(finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).symm
      (finSumFinEquiv (.inr j)), Fin.cast (D.bandCutBoundaryLength_new q f j).symm i⟩ :
      (x : Fin (D.boundaryCount f) ⊕ Fin (D.bandCutExtra q f)) ×
        Fin (Sum.elim (fun b => D.boundaryLength f b*3) (fun _ => 2) x)) = ⟨.inr j,i⟩ := by
    refine Sigma.ext (Equiv.symm_apply_apply _ _) ?_
    exact (Fin.heq_ext_iff (D.bandCutBoundaryLength_new q f j)).mpr rfl
  exact congrArg (fun z => (bandCutSideEquiv q)
    ((Equiv.sumCongr (D.bandCutTriplePositions.trans
      (Equiv.prodCongr D.boundarySide (Equiv.refl _))) (D.bandCutExtraPositions q))
        ((Equiv.sigmaSumDistrib _ _) ⟨f,(Equiv.sumSigmaDistrib (fun x =>
          Fin (Sum.elim (fun b => D.boundaryLength f b*3) (fun _ => 2) x))) z⟩))) he


lemma bandCutBoundaryPositive (f : F) (b : Fin (D.bandCutBoundaryCount q f)) :
    0 < D.bandCutBoundaryLength q f b := by
  obtain ⟨b|j,rfl⟩ := (finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).surjective b
  · rw [bandCutBoundaryLength_old]
    have := D.boundaryPositive f b
    omega
  · rw [bandCutBoundaryLength_new]
    decide

lemma bandCutBoundaryFacet (f : F) (b : Fin (D.bandCutBoundaryCount q f))
    (i : Fin (D.bandCutBoundaryLength q f b)) :
    (D.ports.bandCutPorts q).facet (D.bandCutBoundarySide q ⟨f,b,i⟩)=f := by
  obtain ⟨b|j,rfl⟩ := (finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).surjective b
  · obtain ⟨i,rfl⟩ := (finCongr (D.bandCutBoundaryLength_old q f b).symm).surjective i
    rw [finCongr_apply,bandCutBoundarySide_old]
    exact (D.ports.bandCutLong_facet q _ _).trans (D.boundaryFacet f b i.divNat)
  · obtain ⟨i,rfl⟩ := (finCongr (D.bandCutBoundaryLength_new q f j).symm).surjective i
    rw [finCongr_apply,bandCutBoundarySide_new]
    exact (D.ports.bandCutShort_facet q _).trans (D.bandCutExtra_eq q f j).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence PortAssembly

private lemma tripled_next_zero {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (⟨((finProdFinEquiv (i,(0:Fin 3))).val+1) % (m*3),Nat.mod_lt _ (by omega)⟩ : Fin (m*3)) =
      finProdFinEquiv (i,(1:Fin 3)) := by
  apply Fin.ext
  change (0+3*i.val+1) % (m*3) = 1+3*i.val
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private lemma tripled_next_one {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (⟨((finProdFinEquiv (i,(1:Fin 3))).val+1) % (m*3),Nat.mod_lt _ (by omega)⟩ : Fin (m*3)) =
      finProdFinEquiv (i,(2:Fin 3)) := by
  apply Fin.ext
  change (1+3*i.val+1) % (m*3) = 2+3*i.val
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private lemma tripled_next_two {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (⟨((finProdFinEquiv (i,(2:Fin 3))).val+1) % (m*3),Nat.mod_lt _ (by omega)⟩ : Fin (m*3)) =
      finProdFinEquiv (⟨(i.val+1)%m,Nat.mod_lt _ hm⟩,(0:Fin 3)) := by
  apply Fin.ext
  change (2+3*i.val+1) % (m*3) = 0+3*((i.val+1)%m)
  rw [show 2+3*i.val+1=(i.val+1)*3 by omega,Nat.mul_mod_mul_right]
  omega

variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)

lemma bandCutLong_pair (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b)) (j : Fin 3) :
    bandCutLong q (D.boundarySide ⟨f,b,(finProdFinEquiv (i,j)).divNat⟩,
      (finProdFinEquiv (i,j)).modNat) = bandCutLong q (D.boundarySide ⟨f,b,i⟩,j) := by
  change (fun p : Fin (D.boundaryLength f b) × Fin 3 =>
    bandCutLong q (D.boundarySide ⟨f,b,p.1⟩,p.2))
      (finProdFinEquiv.symm (finProdFinEquiv (i,j)))=_
  rw [finProdFinEquiv.symm_apply_apply]

lemma bandCutLong_next (f : F) (b : Fin (D.boundaryCount f))
    (i : Fin (D.boundaryLength f b*3)) :
    (D.ports.bandCutPorts q).vertexAssembly.corners.boundaryNext
      (bandCutLong q (D.boundarySide ⟨f,b,i.divNat⟩,i.modNat)) =
      bandCutLong q (D.boundarySide ⟨f,b,
        (⟨(i.val+1) % (D.boundaryLength f b*3),Nat.mod_lt _ (by have := D.boundaryPositive f b; omega)⟩ :
          Fin (D.boundaryLength f b*3)).divNat⟩,
        (⟨(i.val+1) % (D.boundaryLength f b*3),Nat.mod_lt _ (by have := D.boundaryPositive f b; omega)⟩ :
          Fin (D.boundaryLength f b*3)).modNat) := by
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  rcases (show j=(0:Fin 3) ∨ j=1 ∨ j=2 by fin_cases j <;> decide) with rfl|rfl|rfl
  · rw [tripled_next_zero (D.boundaryPositive f b) i,bandCutLong_pair,bandCutLong_pair]
    exact D.ports.bandCut_next_first q _
  · rw [tripled_next_one (D.boundaryPositive f b) i,bandCutLong_pair,bandCutLong_pair]
    exact D.ports.bandCut_next_second q _
  · rw [tripled_next_two (D.boundaryPositive f b) i,bandCutLong_pair,bandCutLong_pair,
      D.ports.bandCut_next_last,D.boundaryNext]

lemma bandCutBoundaryNext (f : F) (b : Fin (D.bandCutBoundaryCount q f))
    (i : Fin (D.bandCutBoundaryLength q f b)) :
    (D.ports.bandCutPorts q).vertexAssembly.corners.boundaryNext (D.bandCutBoundarySide q ⟨f,b,i⟩)=
      D.bandCutBoundarySide q ⟨f,b,
        ⟨(i.val+1)%D.bandCutBoundaryLength q f b,Nat.mod_lt _ (D.bandCutBoundaryPositive q f b)⟩⟩ := by
  obtain ⟨b|j,rfl⟩ := (finSumFinEquiv (m:=D.boundaryCount f) (n:=D.bandCutExtra q f)).surjective b
  · obtain ⟨i,rfl⟩ := (finCongr (D.bandCutBoundaryLength_old q f b).symm).surjective i
    rw [finCongr_apply,bandCutBoundarySide_old]
    have he : (⟨((Fin.cast (D.bandCutBoundaryLength_old q f b).symm i).val+1)%
        D.bandCutBoundaryLength q f (finSumFinEquiv (.inl b)),
        Nat.mod_lt _ (D.bandCutBoundaryPositive q f _)⟩ :
          Fin (D.bandCutBoundaryLength q f (finSumFinEquiv (.inl b)))) =
        Fin.cast (D.bandCutBoundaryLength_old q f b).symm
          ⟨(i.val+1)%(D.boundaryLength f b*3),Nat.mod_lt _ (by have := D.boundaryPositive f b; omega)⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast,bandCutBoundaryLength_old]
    rw [he,bandCutBoundarySide_old]
    exact D.bandCutLong_next q f b i
  · obtain ⟨i,rfl⟩ := (finCongr (D.bandCutBoundaryLength_new q f j).symm).surjective i
    rw [finCongr_apply,bandCutBoundarySide_new]
    have he : (⟨((Fin.cast (D.bandCutBoundaryLength_new q f j).symm i).val+1)%
        D.bandCutBoundaryLength q f (finSumFinEquiv (.inr j)),
        Nat.mod_lt _ (D.bandCutBoundaryPositive q f _)⟩ :
          Fin (D.bandCutBoundaryLength q f (finSumFinEquiv (.inr j)))) =
        Fin.cast (D.bandCutBoundaryLength_new q f j).symm
          ⟨(i.val+1)%2,Nat.mod_lt _ (by decide)⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast,bandCutBoundaryLength_new]
    rw [he,bandCutBoundarySide_new]
    exact D.ports.bandCut_next_short q i

/-- The topological inverse handle cut, with complete boundary cycles. The identity seam is an intermediate awaiting proper lower-gallery replacement. -/
def bandCutDiagram : Diagram F (BandCutSeam S) (BandCutVertex V S q) (bandCutArity arity) where
  ports := D.ports.bandCutPorts q
  rank := D.rank
  seamRank := by
    intro s
    rcases s with ⟨s,k⟩|u
    · exact D.seamRank s
    · cases u
      change D.rank (D.bandCutParent q) = ∑ _ : Fin 1, D.rank (D.bandCutParent q)
      simp
  genus f := if f=D.bandCutParent q then D.genus f-1 else D.genus f
  boundaryCount := D.bandCutBoundaryCount q
  boundaryLength := D.bandCutBoundaryLength q
  boundaryPositive := D.bandCutBoundaryPositive q
  boundarySide := D.bandCutBoundarySide q
  boundaryFacet := D.bandCutBoundaryFacet q
  boundaryNext := D.bandCutBoundaryNext q

lemma bandCutDiagram_genus_drop (hg : 0 < D.genus (D.bandCutParent q)) :
    (D.bandCutDiagram q).genus (D.bandCutParent q)+1 = D.genus (D.bandCutParent q) := by
  simp only [bandCutDiagram,ite_true]
  omega

lemma bandCutDiagram_boundary_add :
    (D.bandCutDiagram q).boundaryCount (D.bandCutParent q) = D.boundaryCount (D.bandCutParent q)+1 := by
  simp [bandCutDiagram,bandCutBoundaryCount,bandCutExtra]
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI

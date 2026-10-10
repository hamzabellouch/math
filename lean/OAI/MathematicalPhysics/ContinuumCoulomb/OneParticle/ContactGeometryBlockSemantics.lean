import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactGeometryBlockProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalLocal

namespace OAI

/-! The serialized blocks are the original iterated graph's vertex array,
through the explicit site permutation. No graph relabeling is assumed. -/

noncomputable section
namespace ContinuumCoulomb.ContactGeometryBlockProgram
open ContactMediator

private theorem lookup_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    ((List.ofFn f).drop i.val).headD d = f i := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.headD_cons, List.getElem_ofFn]

theorem block_ofFn {n r : ℕ} (f : Fin n → ContactGadgetSite) (g : Fin r → EdgeInput) :
    block (List.ofFn f) (List.ofFn g) =
      List.ofFn (fun i : Fin (r * n) => ContactPlacedGadgetProgram.position
        (g i.divNat) (f i.modNat)) := by
  apply List.ext_getElem
  · simp only [block, List.length_map, List.length_range, List.length_ofFn, Nat.mul_comm]
  · intro i h₁ h₂
    have hi : i < r * n := by simpa only [List.length_ofFn] using h₂
    have hiq : i / n < r := Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hi)
    have hn : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      simp [this] at hi
    have him : i % n < n := Nat.mod_lt _ hn
    simp only [block, List.getElem_map, List.getElem_range, List.getElem_ofFn, List.length_ofFn]
    rw [lookup_ofFn g defaultEdge ⟨i / n, hiq⟩, List.map_ofFn]
    rw [lookup_ofFn (ContactPlacedGadgetProgram.position (g ⟨i / n, hiq⟩) ∘ f)
      (0, 0) ⟨i % n, him⟩]
    rfl

def literalEdge (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) (e : Fin d.edges) : EdgeInput :=
  ((d.coordinate (d.left e), d.coordinate (d.right e)),
    ContactRationalLocal.input P (ContactMediator.edgeNegative d.bonds e)
      (fun a => ℓ (ContactMediator.encodeEdge d.edges e a)))

def literalInput (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) : Input :=
  (List.ofFn d.coordinate, List.ofFn (literalEdge d P ℓ))

theorem literal_position (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) (e : Fin d.edges) (u : LocalInternal) :
    ContactPlacedGadgetProgram.position (literalEdge d P ℓ e) (localToContact (Sum.inr u)) =
      ContactRationalGlobal.position d P ℓ (siteEquiv d.vertices d.edges (Sum.inr (e, u))) := by
  simp only [ContactRationalGlobal.position, Equiv.symm_apply_apply]
  rw [d.contactEdge_computation]
  rfl

theorem literal_old (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) (i : Fin d.vertices) :
    oldPoint (d.coordinate i) =
      ContactRationalGlobal.position d P ℓ (siteEquiv d.vertices d.edges (Sum.inl i)) := by
  simp only [ContactRationalGlobal.position, Equiv.symm_apply_apply, oldPoint]

theorem literal_length (d : SquareLatticeHeisenberg) (P : ℕ)
    (ℓ : ContactMediator.GlobalEdge d → ℚ) :
    (positions (literalInput d P ℓ)).length = d.vertices + 18 * d.edges := by
  rw [positions_length]
  simp only [literalInput, List.length_ofFn]

def firstIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 2)) : GlobalSite d :=
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inl i.modNat))

def secondIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) : GlobalSite d :=
  let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i.modNat
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inr (Sum.inl st)))

def thirdFirstIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) : GlobalSite d :=
  let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i.modNat
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inr (Sum.inr (Sum.inl st.1, st.2))))

def thirdSecondIndex (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 8)) : GlobalSite d :=
  let st : Fin 4 × Fin 2 := finProdFinEquiv.symm i.modNat
  let su : Fin 2 × Fin 2 := finProdFinEquiv.symm st.1
  siteEquiv d.vertices d.edges (Sum.inr (i.divNat, Sum.inr (Sum.inr (Sum.inr su, st.2))))

theorem firstIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 2)) :
    (firstIndex d i).val = d.vertices + i.val := by
  simp [firstIndex, siteEquiv, encodeSite, MediatorGraph.old, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, finProdFinEquiv]
  omega

theorem secondIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) :
    (secondIndex d i).val = d.vertices + d.edges * 2 + i.val := by
  simp [secondIndex, siteEquiv, encodeSite, MediatorGraph.old, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, spokeIndex, finProdFinEquiv]
  omega

theorem thirdFirstIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 4)) :
    (thirdFirstIndex d i).val = d.vertices + d.edges * 2 + d.edges * 2 * 2 + i.val := by
  simp [thirdFirstIndex, siteEquiv, encodeSite, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, pathIndex, spokeIndex, finProdFinEquiv]
  omega

theorem thirdSecondIndex_val (d : SquareLatticeHeisenberg) (i : Fin (d.edges * 8)) :
    (thirdSecondIndex d i).val =
      d.vertices + d.edges * 2 + d.edges * 2 * 2 + d.edges * 4 + i.val := by
  simp [thirdSecondIndex, siteEquiv, encodeSite, MediatorGraph.fresh,
    MediatorGraph.vertexEquiv, pathIndex, spokeIndex, finProdFinEquiv]
  omega

theorem first_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block firstSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (firstIndex d i)) := by
  rw [firstSites, block_ofFn]
  congr 1
  funext i
  exact literal_position d P ℓ i.divNat (Sum.inl i.modNat)

theorem second_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block secondSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (secondIndex d i)) := by
  rw [secondSites, block_ofFn]
  congr 1
  funext i
  exact literal_position d P ℓ i.divNat (Sum.inr (Sum.inl (finProdFinEquiv.symm i.modNat)))

theorem thirdFirst_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block thirdFirstSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdFirstIndex d i)) := by
  rw [thirdFirstSites, block_ofFn]
  congr 1
  funext i
  let st : Fin 2 × Fin 2 := finProdFinEquiv.symm i.modNat
  exact literal_position d P ℓ i.divNat (Sum.inr (Sum.inr (Sum.inl st.1, st.2)))

theorem thirdSecond_block (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    block thirdSecondSites (List.ofFn (literalEdge d P ℓ)) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdSecondIndex d i)) := by
  rw [thirdSecondSites, block_ofFn]
  congr 1
  funext i
  exact literal_position d P ℓ i.divNat
    (Sum.inr (Sum.inr (Sum.inr (finProdFinEquiv.symm
      (finProdFinEquiv.symm i.modNat : Fin 4 × Fin 2).1),
        (finProdFinEquiv.symm i.modNat : Fin 4 × Fin 2).2)))

theorem literal_blocks (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ
        (siteEquiv d.vertices d.edges (Sum.inl i))) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (firstIndex d i)) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (secondIndex d i)) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdFirstIndex d i)) ++
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ (thirdSecondIndex d i)) := by
  unfold positions literalInput
  rw [List.map_ofFn, first_block, second_block, thirdFirst_block, thirdSecond_block]
  have hold : List.ofFn (oldPoint ∘ d.coordinate) =
      List.ofFn (fun i => ContactRationalGlobal.position d P ℓ
        (siteEquiv d.vertices d.edges (Sum.inl i))) := by
    congr 1
    funext i
    exact literal_old d P ℓ i
  rw [hold]

end ContinuumCoulomb.ContactGeometryBlockProgram

end

end OAI

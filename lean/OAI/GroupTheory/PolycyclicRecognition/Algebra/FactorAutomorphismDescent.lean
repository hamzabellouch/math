import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMultiplication

namespace OAI

/-! # Descending automorphisms through overlapping group factors -/

noncomputable section
namespace PolycyclicRecognition

/-- A commutation identity can be checked on surjective coordinate maps. -/
theorem commutes_of_surjective_coordinates {X Y N D : Type*}
    (eN : X → N) (eD : Y → D) (hn : Function.Surjective eN) (hd : Function.Surjective eD)
    (A : N → N) (B : D → N → N) (a : X → X) (b : Y → X → X)
    (hA : ∀ x, A (eN x) = eN (a x))
    (hB : ∀ y x, B (eD y) (eN x) = eN (b y x))
    (hab : ∀ y x, a (b y x) = b y (a x)) : ∀ d n, A (B d n) = B d (A n) := by
  intro d n
  obtain ⟨y,rfl⟩ := hd d
  obtain ⟨x,rfl⟩ := hn n
  rw [hB,hA,hA,hB,hab]

/-- Invariance of a character can be checked in surjective factor coordinates. -/
theorem character_invariant_of_factor_coordinates {X N D G Q K : Type*}
    [Monoid N] [Monoid D] [Monoid G] [Monoid Q]
    (ι : N →* G) (κ : D →* G) (q : G →* Q) (e : X → N)
    (he : Function.Surjective e)
    (hp : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
    (rot : K → X → X) (act : K → G → G)
    (hq : ∀ x, q (ι (e x)) = 1)
    (ha : ∀ k x d, act k (ι (e x) * κ d) = ι (e (rot k x)) * κ d) :
    ∀ k g, q (act k g) = q g := by
  intro k g
  obtain ⟨⟨n,d⟩,hnd⟩ := hp g
  obtain ⟨x,hx⟩ := he n
  have hg : ι (e x) * κ d = g := (congrArg (fun t => ι t * κ d) hx).trans hnd
  rw [← hg,ha,map_mul,map_mul,hq,hq]

variable {N D G K : Type*} [Group N] [Group D] [Group G] [Group K]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
  (hconj : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
  (hsurj : Function.Surjective (fun p : N × D => ι p.1 * κ p.2))
  (α : K →* MulAut N)
  (hcomm : ∀ k d n, α k (φ d n) = φ d (α k n))
  (hfix : ∀ k n d, ι n = κ d → α k n = n)

private def rotatedFactorHom (k : K) : N ⋊[φ] D →* G :=
  (cartanMultiplication ι κ φ hconj).comp
    (SemidirectProduct.map (α k).toMonoidHom (MonoidHom.id D) (fun d => by
      ext n
      exact hcomm k d n))

include hsurj in
private theorem factorHom_surjective :
    Function.Surjective (cartanMultiplication ι κ φ hconj) := by
  intro g
  obtain ⟨⟨n,d⟩,he⟩ := hsurj g
  exact ⟨⟨n,d⟩,he⟩

include hfix in
private theorem rotatedFactorHom_kernel (k : K) :
    (cartanMultiplication ι κ φ hconj).ker ≤
      (rotatedFactorHom ι κ φ hconj α hcomm k).ker := by
  intro p hp
  have hn : ι p.left = κ p.right⁻¹ := by
    simpa only [map_inv] using (mem_cartanMultiplication_ker ι κ φ hconj p).mp hp
  have hf := hfix k p.left p.right⁻¹ hn
  change ι (α k p.left) * κ p.right = 1
  rw [hf, hn, map_inv, inv_mul_cancel]

/-- The induced endomorphism on the original group. -/
def descendedFactorHom (k : K) : G →* G :=
  (cartanMultiplication ι κ φ hconj).liftOfSurjective
    (factorHom_surjective ι κ φ hconj hsurj)
    ⟨rotatedFactorHom ι κ φ hconj α hcomm k,
      rotatedFactorHom_kernel ι κ φ hconj α hcomm hfix k⟩

@[simp] theorem descendedFactorHom_product (k : K) (n : N) (d : D) :
    descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k (ι n * κ d) =
      ι (α k n) * κ d := by
  exact (cartanMultiplication ι κ φ hconj).liftOfRightInverse_comp_apply _ _ _ ⟨n,d⟩

private theorem descendedFactorHom_one (g : G) :
    descendedFactorHom ι κ φ hconj hsurj α hcomm hfix 1 g = g := by
  obtain ⟨⟨n,d⟩,rfl⟩ := hsurj g
  simp

private theorem descendedFactorHom_mul (k l : K) (g : G) :
    descendedFactorHom ι κ φ hconj hsurj α hcomm hfix (k*l) g =
      descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k
        (descendedFactorHom ι κ φ hconj hsurj α hcomm hfix l g) := by
  obtain ⟨⟨n,d⟩,rfl⟩ := hsurj g
  simp

/-- An action on the first factor commuting with the second factor and
fixing their actual intersection descends to an action on the whole group. -/
def descendedFactorAction : K →* MulAut G where
  toFun k :=
    { toFun := descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k
      invFun := descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k⁻¹
      left_inv g := by
        rw [← descendedFactorHom_mul, inv_mul_cancel, descendedFactorHom_one]
      right_inv g := by
        rw [← descendedFactorHom_mul, mul_inv_cancel, descendedFactorHom_one]
      map_mul' := (descendedFactorHom ι κ φ hconj hsurj α hcomm hfix k).map_mul }
  map_one' := by
    ext g
    exact descendedFactorHom_one ι κ φ hconj hsurj α hcomm hfix g
  map_mul' k l := by
    ext g
    exact descendedFactorHom_mul ι κ φ hconj hsurj α hcomm hfix k l g

@[simp] theorem descendedFactorAction_product (k : K) (n : N) (d : D) :
    descendedFactorAction ι κ φ hconj hsurj α hcomm hfix k (ι n * κ d) =
      ι (α k n) * κ d :=
  descendedFactorHom_product ι κ φ hconj hsurj α hcomm hfix k n d

section Topology
variable [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G]
  [TopologicalSpace K] [IsTopologicalGroup G]

/-- Joint continuity descends through the open factor product. -/
theorem continuous_descendedFactorAction
    (hι : Continuous ι) (hκ : Continuous κ)
    (hα : Continuous (fun p : K × N => α p.1 p.2))
    (hopen : IsOpenMap (fun p : N × D => ι p.1 * κ p.2)) :
    Continuous (fun p : K × G => descendedFactorAction ι κ φ hconj hsurj α hcomm hfix p.1 p.2) := by
  let q : K × (N × D) → K × G := Prod.map id (fun p => ι p.1 * κ p.2)
  have hqc : Continuous q := continuous_id.prodMap ((hι.comp continuous_fst).mul
    (hκ.comp continuous_snd))
  have hqs : Function.Surjective q := Function.Surjective.prodMap Function.surjective_id hsurj
  have hqo : IsOpenMap q := IsOpenMap.id.prodMap hopen
  apply (hqo.isQuotientMap hqc hqs).continuous_iff.mpr
  have he : (fun p : K × G => descendedFactorAction ι κ φ hconj hsurj α hcomm hfix p.1 p.2) ∘ q =
      fun p : K × (N × D) => ι (α p.1 p.2.1) * κ p.2.2 := by
    funext p
    exact descendedFactorAction_product ι κ φ hconj hsurj α hcomm hfix p.1 p.2.1 p.2.2
  rw [he]
  exact (hι.comp (hα.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).mul
    (hκ.comp (continuous_snd.comp continuous_snd))

end Topology
end PolycyclicRecognition

end

end OAI

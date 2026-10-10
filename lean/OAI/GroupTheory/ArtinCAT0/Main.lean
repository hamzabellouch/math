import OAI.GroupTheory.ArtinCAT0.Embeddings

namespace OAI

open scoped Classical
namespace ArtinCAT0
namespace Assembly
@[simp] lemma blockMain_zero (i : Fin 3) : blockMain i (braidGen 39 0)=mainGen (corner i) := by
  have h := blockMain_gen i 0 (by norm_num)
  change blockMain i (braidGen 39 0)=mainGen (blockLetter i 0) at h
  simpa only [blockLetter_zero] using h
@[simp] lemma blockMain_one (i : Fin 3) : blockMain i (braidGen 39 1)=mainGen (corner (i+1)) := by
  have h := blockMain_gen i 1 (by norm_num)
  change blockMain i (braidGen 39 1)=mainGen (blockLetter i 1) at h
  simpa only [blockLetter_one] using h

lemma blockMain_relations (i : Fin 3) : BraidRelations 39 (fun n => blockMain i (braidGen 39 n)) := by
  constructor
  · intro j hj
    simpa only [map_mul] using congrArg (blockMain i) ((braidGroup_relations 39).1 j hj)
  · intro j k hj hk hjk
    exact ((braidGroup_relations 39).2 j k hj hk hjk).map (blockMain i)

universe u
/-- The literal 116-generator presentation has no geometric CAT(0) action. -/
theorem not_geometric (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
    [MulAction MainGroup X] : ¬GeometricAction MainGroup X := by
  classical
  intro hG
  obtain ⟨A,hA,hY⟩ := exists_sublevel_nonempty (X:=X) sentinelMain
  let Y := displacementSublevel (X:=X) sentinelMain A
  let : Nonempty Y := hY
  let : ProperSpace Y := sublevel_properSpace hG.2.1 sentinelMain A
  let := sublevelAction hG.2.1 sentinelMain A
  have hC := geometric_tupleCentralizer hG sentinelMain A hA
  let := MulAction.compHom Y triangleCentralizer
  have hT : GeometricAction TriangleGroup Y := geometric_compHom triangleCentralizer triangleCentralizer_bijective hC
  let y : Y := Classical.choice inferInstance
  have hl (g : TriangleGroup) : stableLengthAt y g=stableLengthAt y.val (triangleMain g) := by
    rw [stableLength_compHom triangleCentralizer]
    exact sublevelAction_stableLength hG.2.1 sentinelMain A y (triangleCentralizer g)
  apply SixSector.no_strict_ratios hT y
  intro i
  have hp : 0<stableLengthAt y.val ((blockMain i (braidGen 39 0))^2) := by
    rw [blockMain_zero]
    exact generator_square_positive explicitMatrix hG y.val (corner i)
  have hr := (braid_forty_ratio hG y.val (blockMain_relations i) hp).2.1
  simpa only [hl,triangleH,map_pow,map_mul,triangleMain_gen,blockMain_zero,blockMain_one] using hr
end Assembly

universe u

theorem main :
    (∀ s t : Letters, explicitMatrix s t = explicitMatrix t s) ∧
    (∀ s : Letters, explicitMatrix s s = 1) ∧
    (∀ s t : Letters, s ≠ t →
      explicitMatrix s t = 2 ∨ explicitMatrix s t = 3 ∨ explicitMatrix s t = ⊤) ∧
    (∀ (X : Type u) [MetricSpace X] [ProperSpace X] [Nonempty X]
      [MulAction (ArtinGroup explicitMatrix) X],
      ¬ GeometricAction (ArtinGroup explicitMatrix) X) := by
  exact ⟨explicitMatrix_symmetric,explicitMatrix_diagonal,explicitMatrix_values,Assembly.not_geometric⟩
end ArtinCAT0

end OAI

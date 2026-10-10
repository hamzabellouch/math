import OAI.MeasureTheory.Falconer.Incidence.LeafCenterIncidence
import OAI.MeasureTheory.Falconer.Recursion.ProfileEndpointBound

namespace OAI

/-! Transport the original pencils to the selected terminal centers by one
common line map. Their union cardinality cannot increase. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem quarterEndpointSet_root {N : ℕ} (Q : DyadicCube 2)
    {C : Finset (CellPath 2)} (hC : C ⊆ cubePaths 2 N) :
    quarterEndpointSet Q C 0 N [] = C.image (quarterEndpointPoint Q 0 []) := by
  have he : C.image (List.take N) = C := by
    ext p
    constructor
    · rintro hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hlen := (mem_cubePaths _ _ _).mp (hC hq)
      simpa only [← hlen,List.take_length] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p,hp,by rw [← (mem_cubePaths _ _ _).mp (hC hp),List.take_length]⟩
  rw [quarterEndpointSet,prefixChildren,prefixFiber_zero,he]

theorem transport_pencils_to_leaf_centers {N : ℕ} (Q : DyadicCube 2)
    (hQ : Q.side = 1) (hcenter : Q.center = 0)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    {C : Finset (CellPath 2)} (hCP : C ⊆ P.image l)
    {δ s K W a b : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hsmall : 16*δ ≤ 1/(2:ℝ)^N) (hsize : b ≤ W*a) (hbudget : K*4^s ≤ W)
    (V : Space 2 → Finset (Space 2))
    (hV : ∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
      InBoundedLineChart (V x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (V x) ∧
      NormalizedFiniteBallBound δ s K (V x) ∧
      ∀ u ∈ V x, |u 0| ≤ 1/2 ∧ TubeIncident δ x u) :
    ∃ T : Space 2 → Finset (Space 2),
      QuarterPencilData (1/(2:ℝ)^(N+2)) s W a (quarterEndpointSet Q C 0 N []) T ∧
      (((quarterEndpointSet Q C 0 N []).biUnion T).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := by
  have hCN : C ⊆ cubePaths 2 N := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hCP hr)
    exact (hleaf x hx).1
  let F := fun x => quarterEndpointPoint Q 0 [] (l x)
  let Z := quarterEndpointSet Q C 0 N []
  have hZP : Z ⊆ P.image F := by
    dsimp [Z]
    rw [quarterEndpointSet_root Q hCN]
    intro z hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hCP hr)
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  let q := Function.invFunOn F (P : Set (Space 2))
  have hq (z : Space 2) (hz : z ∈ Z) : q z ∈ P ∧ F (q z) = z :=
    Function.invFunOn_pos (Finset.mem_image.mp (hZP hz))
  let A := localCellLine 4 0 0
  let T := fun z => (V (q z)).image A
  have hwidth : (1/(2:ℝ)^N)/4 = 1/(2:ℝ)^(N+2) := by rw [pow_add]; norm_num; ring
  have hδwidth : δ/4 ≤ 1/(2:ℝ)^(N+2) := by rw [← hwidth]; linarith
  refine ⟨T,?_,?_⟩
  · intro z hz
    obtain ⟨hqP,hqz⟩ := hq z hz
    obtain ⟨hlo,hhi,hchart,hsep,hball,hinc⟩ := hV (q z) hqP
    have hcard : ((T z).card:ℝ) = ((V (q z)).card:ℝ) := by
      dsimp [T,A]
      rw [Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]
    refine ⟨hlo.trans_eq hcard.symm,hcard.trans_le (hhi.trans hsize),
      localCellLine_four_chart _ hchart,?_,?_,?_⟩
    · rw [← hwidth]
      exact localCellLine_four_separated _ hsep
    · have hb := localCellLine_four_regular hδ hs hK _ hball
      intro w r hr hr1
      have hh := hb w r (hδwidth.trans hr) hr1
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ δ/4).trans (hδwidth.trans hr)) _)) (Nat.cast_nonneg _))
    · intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      have hv' := hinc v hv
      refine ⟨hv'.1,?_⟩
      have hh := root_leaf_quarter_incident Q hQ (hleaf (q z) hqP).1 hδ.le
        (hleaf (q z) hqP).2 hv'.1 hv'.2 hsmall
      simp only [hcenter,PiLp.zero_apply] at hh
      change TubeIncident _ (F (q z)) (A v) at hh
      simpa only [hqz] using hh
  · apply Nat.cast_le.mpr
    apply le_trans (Finset.card_le_card (show Z.biUnion T ⊆ (P.biUnion V).image A from ?_))
      Finset.card_image_le
    intro u hu
    obtain ⟨z,hz,hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨q z,(hq z hz).1,hv⟩)

end Falconer

end OAI

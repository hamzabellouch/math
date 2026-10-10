import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Region

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPlanarCorner
open Set Topology Metric

def positiveHalfAxis : Set (ℝ × ℝ) := {p | 0≤p.1 ∧ p.2=0}

lemma slit_box_connected {r : ℝ} (hr : 0<r) :
    IsConnected (CannonFaceIncidence.openBox r\positiveHalfAxis) := by
  let L : Set (ℝ × ℝ) := Ioo (-r) 0 ×ˢ Ioo (-r) r
  have hL : IsConnected L := (isConnected_Ioo (neg_neg_of_pos hr)).prod
    (isConnected_Ioo (by linarith : -r<r))
  have hm (b : Bool) : (L∩CannonFaceIncidence.halfBox r b).Nonempty := by
    cases b
    · refine ⟨(-r/2,-r/2),?_,?_⟩
      · change (-r< -r/2 ∧ -r/2<0) ∧ (-r< -r/2 ∧ -r/2<r)
        constructor <;> constructor <;> linarith
      · change (-r< -r/2 ∧ -r/2<r) ∧ (-r< -r/2 ∧ -r/2<0)
        constructor <;> constructor <;> linarith
    · refine ⟨(-r/2,r/2),?_,?_⟩
      · change (-r< -r/2 ∧ -r/2<0) ∧ (-r<r/2 ∧ r/2<r)
        constructor <;> constructor <;> linarith
      · change (-r< -r/2 ∧ -r/2<r) ∧ (0<r/2 ∧ r/2<r)
        constructor <;> constructor <;> linarith
  have he : CannonFaceIncidence.openBox r\positiveHalfAxis=
      (L∪CannonFaceIncidence.halfBox r false)∪CannonFaceIncidence.halfBox r true := by
    ext p
    simp only [CannonFaceIncidence.openBox,CannonFaceIncidence.halfBox,L,positiveHalfAxis,
      Bool.false_eq_true,↓reduceIte,mem_sdiff,mem_ofPred_eq,mem_prod,mem_Ioo,mem_union]
    constructor
    · rintro ⟨⟨hx,hy⟩,hn⟩
      by_cases hpx : p.1<0
      · exact Or.inl (Or.inl ⟨⟨hx.1,hpx⟩,hy⟩)
      · have hpy : p.2≠0 := fun h => hn ⟨le_of_not_gt hpx,h⟩
        rcases lt_or_gt_of_ne hpy with hp|hp
        · exact Or.inl (Or.inr ⟨hx,hy.1,hp⟩)
        · exact Or.inr ⟨hx,hp,hy.2⟩
    · rintro ((⟨hx,hy⟩|⟨hx,hy⟩)|⟨hx,hy⟩)
      · exact ⟨⟨⟨hx.1,hx.2.trans hr⟩,hy⟩,fun h => hx.2.not_ge h.1⟩
      · exact ⟨⟨hx,hy.1,hy.2.trans hr⟩,fun h => hy.2.ne h.2⟩
      · exact ⟨⟨hx,(neg_neg_of_pos hr).trans hy.1,hy.2⟩,fun h => hy.1.ne' h.2⟩
  rw [he]
  apply IsConnected.union _ (IsConnected.union (hm false) hL (CannonFaceIncidence.halfBox_connected hr false))
    (CannonFaceIncidence.halfBox_connected hr true)
  obtain ⟨p,hpL,hpT⟩ := hm true
  exact ⟨p,Or.inl hpL,hpT⟩

lemma straight_ray_chart (x u : ℂ) (hu : u≠0) :
    ∃ H : (ℝ × ℝ) ≃ₜ ℂ, H (0,0)=x ∧
      H '' positiveHalfAxis={z | ∃ s : ℝ, 0 ≤ s ∧ z=x+s•u} := by
  let H := (Complex.equivRealProdCLM.toHomeomorph.symm.trans (Homeomorph.mulLeft₀ u hu)).trans
    (Homeomorph.addLeft x)
  have ht (t : ℝ) : H (t,0)=x+t•u := by
    change x+u*Complex.equivRealProdCLM.symm (t,0)=x+t•u
    congr 1
    rw [Complex.real_smul]
    have he : Complex.equivRealProdCLM.symm (t,0)=(t:ℂ) := by apply Complex.ext <;> rfl
    rw [he,mul_comm]
  refine ⟨H,by simpa using ht 0,?_⟩
  ext z
  constructor
  · rintro ⟨⟨s,t⟩,⟨hs,ht₀⟩,rfl⟩
    change t=0 at ht₀
    subst t
    exact ⟨s,hs,ht s⟩
  · rintro ⟨s,hs,hz⟩
    exact ⟨(s,0),⟨hs,rfl⟩,(ht s).trans hz.symm⟩
end CannonPlanarCorner

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

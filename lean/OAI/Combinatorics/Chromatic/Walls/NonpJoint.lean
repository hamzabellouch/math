import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteSignCharts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RootTruncation
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def nonpSupportFrame (w : M →+ ℤ) (h : M →+ ℝ) (P : AddSubmonoid M) (n : ℤ) : AddSubmonoid M where
  carrier:={m | m=0 ∨ (0<w m ∧ ((w m<n ∨ (w m=n ∧ h m=0)) → m∈P))}
  zero_mem':=Or.inl rfl
  add_mem':=by
    intro a b ha hb
    rcases ha with rfl | ⟨ha,haP⟩
    · simpa using hb
    rcases hb with rfl | ⟨hb,hbP⟩
    · exact Or.inr ⟨by simpa using ha,by simpa using haP⟩
    refine Or.inr ⟨by simpa only [map_add] using add_pos ha hb,?_⟩
    intro hs
    have hsum : w a+w b≤n:=by
      rcases hs with hs | ⟨hs,_⟩
      · simpa only [map_add] using le_of_lt hs
      · exact le_of_eq (by simpa only [map_add] using hs)
    exact P.add_mem (haP (Or.inl (by omega))) (hbP (Or.inl (by omega)))

lemma nonpSupportFrame_target {w : M →+ ℤ} {h : M →+ ℝ} {P : AddSubmonoid M} {n : ℤ}
    {m : M} (hm : m∈nonpSupportFrame w h P n) (hw : w m=n) (hh : h m=0) : m∈P := by
  rcases hm with rfl | hm
  · exact P.zero_mem
  · exact hm.2 (Or.inr ⟨hw,hh⟩)

omit [Algebra ℚ R] in
lemma completedListProduct_congr_through {A : Type*} (l : List A)
    (F G : A → CompletedPositive v Ω C) (N : ℕ)
    (H : ∀a∈l,∀j≤N,coeff j (F a).val=coeff j (G a).val) :
    ∀j≤N,coeff j (completedListProduct v Ω C l F).val=
      coeff j (completedListProduct v Ω C l G).val := by
  intro j hj
  exact PowerSeriesSplit.product_coeff_congr _ _ l j (fun a ha i hi=>H a ha i (hi.trans hj))

lemma planar_joint_support (e : M →+ E) (he : Function.Injective e)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
    (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
    (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
    (r s : E) (hr : 0<L r) (hrs : B r s≠0)
    (F : CompletedPositive v Ω C)
    (hF : ∀j,coeff j F.val∈supportedSubring v Ω (planeRoots e r s))
    (N : ℕ) (P : AddSubmonoid M)
    (HI : ∀p d,0<d → d≤N → HasRootDegree C d p → p∈planeRoots e r s →
      ∀j≤N,coeff j (chartZero v Ω C (incomingCovector Ω p) F).val∈supportedSubring v Ω P)
    (h : M →+ ℝ) :
    ∀j≤N,coeff j (chartZero v Ω C h F).val∈supportedSubring v Ω P := by
  classical
  obtain ⟨l,hl,hpair,hRay,hfact⟩:=planar_joint_factorization v Ω C e he B hB hcomp L hdeg r s hr hrs F hF N
  let J (p : M):=chartZero v Ω C (incomingCovector Ω p) F
  let K (p : M):=completedCut v Ω C N (J p)
  let G:=completedListProduct v Ω C l K
  have hK : ∀p∈l,∀j,coeff j (K p).val∈supportedSubring v Ω P:=by
    intro p hp
    obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    exact completedCut_supported v Ω C N (J p) P (HI p d hd hdN hdp hpP)
  have hG : ∀j,coeff j G.val∈supportedSubring v Ω P:=completed_list_supported v Ω C l K P hK
  have hFG : ∀j≤N,coeff j F.val=coeff j G.val:=by
    intro j hj
    refine (hfact j hj).trans ?_
    apply completedListProduct_congr_through v Ω C l J K N ?_ j hj
    intro p hp i hi
    exact (coeff_cut_of_le (J p).val hi).symm
  have hchart:=chartZero_congr_through v Ω C h F G N hFG
  intro j hj
  rw [hchart j hj]
  exact (chartThree_supported v Ω C h P G hG).2.1 j
end
end ElementaryPositivity.QuantumTorus

end

end OAI

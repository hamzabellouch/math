import Mathlib
import OAI.Combinatorics.UniformKServer.ParkedTransport

namespace OAI

                                        
section

/-! A causal one-step extension with a literal labeled metric configuration.
No independence between old parent and child counts is imposed. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n} {X : Type*} [PseudoMetricSpace X]

theorem mean_add (L : Law) (f g : L.State→ℝ) :
    mean L (fun s=>f s+g s)=mean L f+mean L g := by
  simp only [mean,mul_add,sum_add_distrib]

theorem mean_mul (L : Law) (c : ℝ) (f : L.State→ℝ) :
    mean L (fun s=>c*f s)=c*mean L f := by
  simp only [mean,mul_sum]
  exact sum_congr rfl (fun s _=>by ring)

theorem metric_step (w : Vertex n→ℝ) (hw : ∀ v,0≤w v)
    (hsep : ∀ v,v≠0 → 22*w v≤w (S.parent v))
    (a b : Allocation S k) (f g : Vertex n→X) (G : ℝ) (hG : 0≤G)
    (hgeo : ∀ u v,0<park S a.amount u → 0<park S b.amount v → u≠v →
      dist (f u) (g v)≤G*pathCost (S:=S) w u v)
    (L : Law) (x : L.State→Vertex n→ℤ)
    (hx : ∀ s,Rounded a (x s))
    (hm : ∀ v,mean L (fun s=>(x s v:ℝ))=a.amount v)
    (R : ∀ s,Realization (k:=k) (S:=S) (x s)) :
    ∃ E : Extension L n,
      (∀ s,Rounded b (E.value s)) ∧
      (∀ v,mean E.law (fun s=>(E.value s v:ℝ))=b.amount v) ∧
      ∃ T : ∀ s,Realization (k:=k) (S:=S) (E.value s),
        mean E.law (fun s=>∑ i,dist (f ((R (E.original s)).tuple i)) (g ((T s).tuple i)))≤
        G*132*variation w a b+∑ v,park S b.amount v*commonDistance a b f g v := by
  obtain ⟨E,he,hmE,hmove⟩ := tree_rounding S w hw hsep a b L x hx hm
  let U (s : E.law.State) := realize b (E.value s) (he s)
  have hp (s : E.law.State) := parked_matching a b w hw f g G hG hgeo
    (hx (E.original s)) (he s) (R (E.original s)) (U s)
  choose π hπ using hp
  let T (s : E.law.State) := (U s).permute (π s)
  refine ⟨E,he,hmE,T,?_⟩
  have heach (s : E.law.State) :
      (∑ i,dist (f ((R (E.original s)).tuple i)) (g ((T s).tuple i)))≤
      G*(∑ v : Vertex n,if v=0 then 0 else w (S.parent v)*|(E.value s v:ℝ)-x (E.original s) v|)+
      ∑ v,(intPark S (E.value s) v:ℝ)*commonDistance a b f g v := hπ s
  have h := mean_mono E.law heach
  have hfirst : mean E.law (fun s=>G*(∑ v : Vertex n,if v=0 then 0 else
      w (S.parent v)*|(E.value s v:ℝ)-x (E.original s) v|))=G*movement S w L x E := by
    rw [mean_mul,mean_sum]
    congr 1
    unfold movement
    apply sum_congr rfl
    intro v _
    by_cases hv : v=0
    · simp [hv,mean_const]
    · simp only [hv,ite_false,mean_mul]
  have hsecond : mean E.law (fun s=>∑ v,(intPark S (E.value s) v:ℝ)*commonDistance a b f g v)=
      ∑ v,park S b.amount v*commonDistance a b f g v := by
    rw [mean_sum]
    apply sum_congr rfl
    intro v _
    simp only [mul_comm _ (commonDistance a b f g v),mean_mul,mean_intPark E.law E.value hmE]
  rw [mean_add,hfirst,hsecond] at h
  have hg := mul_le_mul_of_nonneg_left hmove hG
  nlinarith only [h,hg]

end UniformKServer.TreeRounding

end


end

end OAI

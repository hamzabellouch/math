import OAI.Combinatorics.HadwigerCounterexample.FinitePredictions

namespace OAI

/-! # Predicted Dual Coefficients -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Module LinearMap
open scoped BigOperators Topology
variable {p:Shape} {r n:ℕ}
namespace StatusAnalysis
namespace DualAnalysis

variable {d e:Rates} {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}

open PredictionClass

private def scaled (a:F) (w:RhymeSet n):RhymeSet n :=
  ⟨a*w.bit,a • w.coal,a*w.headBit,a*w.gamma⟩
def Pulsar.mult (g:Pulsar p r)(a:F) : Pulsar p r := fun i j k=>a*g i j k

private theorem scaleShot (i:Nodes) (z:RhymeSet (d i)) (A:Finset (Label p.b)) (f:Pulsar p r)
    {ε:ℝ}(hc:0≤ε)(h:praise u s i A z f ε) (k:F) :
    praise u s i A (scaled k z) (f.mult k) ε := by
  classical
  rcases bit_cases k with ht|ht
  · subst k; intro x hx ha
    unfold shot Pulsar.mult RhymeSet.soot RhymeSet.read scaled
    simp only [zero_mul,zero_smul,zero_dotProduct,add_zero, ne_eq,not_true_eq_false,pr_false,avg_const,
      mul_zero]; exact hc
  subst k; rw [show f.mult 1=f from (by unfold Pulsar.mult; simp only [one_mul]), show scaled 1 z=z from (by unfold scaled; simp)] ; exact h

private theorem center_tri (w:Wgt (Fin r)) (k:F)
    (f g h:Fin r→ F) (b:F) (hw:IsLaw w)
    (x y:ℝ)
    (hx:pr w (fun i=>h i≠f i)≤x) (hy:pr w (fun i=>h i+b*k≠g i)≤y):
    pr w (fun i=> f i+g i≠ b*k)≤ x+y := by
  classical
  let P i:= h i≠f i; let Q i:=h i+b*k≠g i
  have hi i (h': f i+g i≠b*k):P i∨Q i:= by
    by_contra! hh
    apply h'
    rw [← not_not.mp hh.1,← not_not.mp hh.2,←add_assoc,char_two,zero_add]
  exact ((pr_mono hw.nz hi).trans (pr_or_le hw.nz)).trans (add_le_add hx hy)

abbrev styles (d:Rates) := ∀ i:Nodes, Cell (d i)

structure PredictionData (p:Shape) (d e:Rates) (r:ℕ) where
  α : Party
  g : Nodes→ Pulsar p r
  X : styles d
  Y : styles e

def PredictionData.colored (v:PredictionData p d e r) (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
    (A B:Stalls p) (ε:ℝ) :=
    (∀ i,praise u s i (A i) (yokeSet (v.X i) (v.α i)) (v.g i) ε) ∧
    (∀ i,praise u t i (B i) (yokeSet (v.Y i) (v.α i)) (v.g i) ε)

def ChorusCost (w:PredictionData p d e r) (v:DualCoefficients d e) (i:Grid) (u:Terrain p r)
    (l:Tag p.g) (q:F) :=
  pr (u l q) (fun k=>v.left i.2*w.g i.1 l q k+v.right i.1*w.g i.2 l q k≠v.gam i*q)

set_option maxHeartbeats 900000 in
theorem duet_edge {δ β a ε:ℝ}
    (v:PredictionData p d e r) (z:DualCoefficients d e) (i:Grid)
    (hp:3≤p.g) (hu:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (A B:Stalls p)
    (hv:v.colored u s t A B a) (hA:(A i.1).card<Fintype.card (Label p.b))
    (hB:(B i.2).card<Fintype.card (Label p.b))
    (hh:counsel u s t i (A i.1) (B i.2) (leftChime z i) (rightChime z i) ε)
    (hε:0 ≤ ε) (hz:0 ≤ a) (hb:0≤β) (hi :3*ε+a<1/2*β) :
    z.north i=z.left i.2 • v.X i.1 ∧ z.south i=z.right i.1 • v.Y i.2 ∧
      z.hed i=z.left i.2*firstBit v.α i.1 ∧ z.hed i=z.right i.1*firstBit v.α i.2 ∧
        ∀ l q,ChorusCost v z i u l q≤2*(3*ε+a) := by
  classical
  obtain ⟨P,h1,h2⟩:= paeans u s t hu hs ht i (A i.1) (B i.2) hA hB hp _ _ ε hε hh
  let X:= z.left i.2; let Y:=z.right i.1
  have h3:=scaleShot i.1 _ _ _ hz (hv.1 i.1) X
  have h4:=scaleShot i.2 _ _ _ hz (hv.2 i.2) Y
  have heq:=unison hp hu hs i.1 _ _ _ _ _ _ (by rw [union_idempotent]; exact hA)
    h1 h3 (show X=X*1 by rw [mul_one]) hi hb
  obtain ⟨hC,hD,hE⟩:=heq
  obtain ⟨hF,hG,hH⟩:=unison hp hu ht i.2 _ _ _ _ _ _ (by rw [union_idempotent]; exact hB)
    h2 h4 (show Y=Y*1 by rw [mul_one]) hi hb
  refine ⟨hC,hF,hD,hG,fun l q=>?_⟩
  unfold ChorusCost
  rw [two_mul]
  apply center_tri (w:=u l q) (k:=q) (h:=P l q) _ _ (b:=z.gam i) (hu.1 l q)
    (3*ε+a) (3*ε+a)
  · have ht:=hE l q
    simpa only [leftChime,scaled,yokeSet,mul_zero,zero_mul,add_zero,Pulsar.mult] using ht
  have ht:=hH l q
  simpa only [rightChime,scaled,yokeSet,mul_zero,zero_mul,add_zero,Pulsar.mult] using ht
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI

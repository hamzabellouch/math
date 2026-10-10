import Mathlib
import OAI.Combinatorics.KServer.CausalRounding

namespace OAI

/-! Absolute constants for the unconditional finite-law endpoint. No metric,
finite-tree depth, horizon, law or initial tuple enters these coefficients. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
open ActualCharges RankTracking JointExperiment JointAllocation
attribute [local instance] Classical.propDecidable Classical.decEq

def core : ℝ := (6/5:ℝ)*72
def cutoff : ℝ := 7*core/Real.log 2+2*core
def quotaMultiplier : ℝ := 15840+640*(6/5:ℝ)
def keyMultiplier : ℝ := quotaMultiplier*(384*localConstant)+160*core*289
def optMultiplier : ℝ := 160*cutoff/3

def embA : ℝ := 147*TierProcess.tierDrift+2*EmbeddedCost.heavyDrift
def embB : ℝ := 98/TierProcess.heavyGamma+32+2/3+8
def embC : ℝ := 32+31440+60/Real.log (1+TierProcess.heavyDelta)+
  1050*(60/Real.log (1+TierProcess.heavyDelta)+60)
def embeddingMultiplier : ℝ := |embA|+|embB|+|embC|+1
def competitiveMultiplier : ℝ := keyMultiplier*embeddingMultiplier+optMultiplier

lemma constants_pos : 0<core ∧ 0<cutoff ∧ 0<quotaMultiplier ∧ 0<keyMultiplier ∧
    0<optMultiplier ∧ 0<embeddingMultiplier ∧ 0<competitiveMultiplier:=by
  have hc:0<core:=by norm_num [core]
  have hl:0<Real.log 2:=Real.log_pos (by norm_num)
  have hcut:0<cutoff:=by unfold cutoff; positivity
  have hq:0<quotaMultiplier:=by norm_num [quotaMultiplier]
  have hlocal:=output_constants_nonneg.2.2.2
  have hkey:0<keyMultiplier:=by unfold keyMultiplier; positivity
  have ho:0<optMultiplier:=by unfold optMultiplier; positivity
  have he:0<embeddingMultiplier:=by unfold embeddingMultiplier; positivity
  refine ⟨hc,hcut,hq,hkey,ho,he,?_⟩
  unfold competitiveMultiplier
  positivity

lemma embedding_coefficient {k:ℕ} (hk:1≤(k:ℝ)):
    EmbeddedCost.tierCoefficient k+EmbeddedCost.heavyCoefficient k+EmbeddedCost.spatialCoefficient k≤
      embeddingMultiplier*ActualCaps.ell k:=by
  have he:1≤ActualCaps.ell k:=ActualCaps.ell_ge_one hk
  have hkpos:0<(k:ℝ):=by linarith
  have hlog:0≤Real.log (k:ℝ):=Real.log_nonneg hk
  have hle:Real.log (k:ℝ)≤ActualCaps.ell k:=by
    have hh:=Real.log_le_log hkpos (show (k:ℝ)≤(k:ℝ)+1 by linarith)
    unfold ActualCaps.ell
    linarith
  have hA:embA*ActualCaps.ell k≤|embA| *ActualCaps.ell k:=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hB:embB≤|embB| *ActualCaps.ell k:=by
    calc
      embB≤|embB|:=le_abs_self _
      _≤|embB| *ActualCaps.ell k:=by nlinarith [abs_nonneg embB]
  have hC:embC*Real.log (k:ℝ)≤|embC| *ActualCaps.ell k:=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hlog).trans
      (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
  have identity:EmbeddedCost.tierCoefficient k+EmbeddedCost.heavyCoefficient k+EmbeddedCost.spatialCoefficient k=
      embA*ActualCaps.ell k+embB+embC*Real.log (k:ℝ):=by
    unfold EmbeddedCost.tierCoefficient EmbeddedCost.heavyCoefficient EmbeddedCost.spatialCoefficient
      embA embB embC ActualCaps.ell
    ring
  rw [identity]
  unfold embeddingMultiplier
  nlinarith
end KServer.GlobalEndpoint

end


/-! Main finite construction at separation ratio 32. Initial inventories are
explicitly independent of both the request law and its horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
open ActualCharges RankTracking JointExperiment JointAllocation
attribute [local instance] Classical.propDecidable Classical.decEq

def radii (R:ℝ) (L:ℕ) (d:Fin L):ℝ:=R/(32:ℝ)^(d.val+1)
lemma radii_pos {R:ℝ} {L:ℕ} (hR:0<R) (d:Fin L):0<radii R L d:=
  div_pos hR (by positivity)

def quotaInventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  2*localConstant*ActualCaps.ell k*
    HierarchicalQuota.treeInventory (LevelKeys.Key Y k) k (fun d=>R/(32:ℝ)^d) L
def chargeInventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  core*(∑ d:Fin L,radii R L d)*(Fintype.card (LevelKeys.Key Y k)*
    (288*((k:ℝ)+1)*(1+ActualCaps.ell k)))
def potentialInventory (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=core*k*(∑ d:Fin L,radii R L d)
def embeddingInventory (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  (299+Fintype.card (LevelKeys.Tier k))*EmbeddedCost.inventory k (R/(32:ℝ)^L) 32 L
def baseInventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  quotaMultiplier*quotaInventory Y k R L+160*chargeInventory Y k R L+
    160*potentialInventory k R L+(k:ℝ)*R
def inventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  baseInventory Y k R L+keyMultiplier*ActualCaps.ell k*embeddingInventory k R L

variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y)) (hk:1≤(k:ℝ))

lemma opt_nonneg : 0≤EmbeddedCost.opt s law:=
  sum_nonneg (fun σ _=>mul_nonneg (law.property.1 σ) (optimalCost_nonneg s (List.ofFn σ)))

include hk in
lemma cost_by_keys {R:ℝ} (hR:0<R) (hL:0<L) (hdia:∀ x y:Y,dist x y≤R)
    (hf:∀ x y:Y,dist x y≤20*(R/(32:ℝ)^L)→x=y):
    ∃ A:Policy k Y,StronglyLazy s A ∧
      (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
        keyMultiplier*ActualCaps.ell k*
          total (weight law (radii_pos (L:=L) hR)) H
            (JointBudget.stepKey s law (radii_pos (L:=L) hR))+
        optMultiplier*ActualCaps.ell k*EmbeddedCost.opt s law+baseInventory Y k R L:=by
  let r:=radii R L
  have hr:∀ d:Fin L,0<r d:=fun d=>div_pos hR (by positivity)
  let Q:=total (weight law hr) H (JointBudget.stepQuota s law hr hk R 32)
  let K:=total (weight law hr) H (JointBudget.stepKey s law hr)
  let P:=total (weight law hr) H (fun t ω=>∑ v:JointBudget.Node (Y:=Y) (k:=k) (L:=L),
    PrefixTree.weight (LevelKeys.Key Y k) L R 32 v*
      |park s law hr hk (t+1) ω v-park s law hr hk t ω v|)
  let T:=total (weight law hr) H (JointHeavy.travel s law hr hk)
  let Ch:=total (weight law hr) H (JointHeavy.charge s law hr hk)
  have hQ0:0≤Q:=total_nonneg (weight_nonneg law hr)
    (JointBudget.stepQuota_nonneg s law hr hk hR.le (by norm_num))
  have hK0:0≤K:=total_nonneg (weight_nonneg law hr) (JointBudget.stepKey_nonneg s law hr)
  have hell:=ActualCaps.ell_ge_one hk
  have hQ:Q≤384*localConstant*ActualCaps.ell k*K+quotaInventory Y k R L:=by
    have hh:=JointBudget.quota_bound s law hr hk hR.le (by norm_num : (2:ℝ)≤32)
      (fun d=>rfl) H
    norm_num only [mul_one,show (12:ℝ)*32=384 by norm_num] at hh
    exact hh
  have hP:P≤2*Q:=by
    have hh:=total_mono (weight_nonneg law hr) (N:=H) (fun t ω=>
      JointBudget.park_bound s law hr hk hR.le (by norm_num : (0:ℝ)<32) t ω)
    rw [total_mul] at hh
    change P≤(1+1/32:ℝ)*Q at hh
    linarith
  have hc:Ch≤core*288*ActualCaps.ell k*K+2*(6/5:ℝ)*P+chargeInventory Y k R L:=by
    have hh:=JointHeavy.charge_bound s law hr hk H (PrefixTree.weight (LevelKeys.Key Y k) L R 32)
      (PrefixTree.weight_nonneg _ L hR.le (by norm_num)) (by
        intro d a v hv
        dsimp only [r,radii,PrefixTree.weight]
        rw [PrefixTree.band_depth _ L d.val (HeavyAnchorDynamics.slot (k:=k) a) hv])
    exact hh
  have hrad:∀ d:Fin L,r d=ParkedCoefficients.radius (R/32) 32 d.val:=by
    intro d
    dsimp only [r,radii,ParkedCoefficients.radius]
    rw [pow_succ]
    field_simp
  have hT:T≤4*core*K+(4*cutoff/3)*ActualCaps.ell k*EmbeddedCost.opt s law+
      4*Ch+4*potentialInventory k R L:=by
    have hh:=JointHeavy.travel_raw s law hr hk (div_nonneg hR.le (by norm_num))
      (by norm_num : (2:ℝ)≤32) hrad (C:=cutoff*ActualCaps.ell k) (by
        dsimp only [cutoff,core,ActualCaps.ell]
        ring_nf
        exact le_rfl)
    rw [JointEmbedding.hidden_cost s law hr] at hh
    change T≤4*core*K+4*(cutoff*ActualCaps.ell k)/3*EmbeddedCost.opt s law+
      4*Ch+4*potentialInventory k R L at hh
    nlinarith only [hh]
  obtain ⟨A,hA,hcost⟩:=JointPolicy.exists_policy s law hr hk hR.le (by norm_num : (22:ℝ)≤32)
    hdia (fun d=>rfl) hL (by
      intro x y hxy
      apply hf x y
      have hlast:(⟨L-1,by omega⟩:Fin L).val+1=L:=by simp only; omega
      simpa only [r,radii,hlast] using hxy)
  refine ⟨A,hA,?_⟩
  change (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
    keyMultiplier*ActualCaps.ell k*K+optMultiplier*ActualCaps.ell k*EmbeddedCost.opt s law+
      baseInventory Y k R L
  change _≤15840*Q+40*T+(k:ℝ)*R at hcost
  have hcoreK:core*K≤core*ActualCaps.ell k*K:=by
    have hp:=mul_nonneg constants_pos.1.le hK0
    nlinarith
  have hq:=mul_le_mul_of_nonneg_left hQ constants_pos.2.2.1.le
  dsimp only [keyMultiplier,optMultiplier,baseInventory,quotaMultiplier] at hq ⊢
  norm_num only [core] at hcoreK hc hT ⊢
  nlinarith [hc,hP,hT,hcost,hcoreK,hq]

include hk in
lemma finite_geometric {R:ℝ} (hR:0<R) (hL:0<L) (hdia:∀ x y:Y,dist x y≤R)
    (hf:∀ x y:Y,dist x y≤20*(R/(32:ℝ)^L)→x=y):
    ∃ D:ℝ,0≤D ∧ ∀ H:ℕ,∀ law:FiniteDistribution (Fin H→Y),
      ∃ A:Policy k Y,StronglyLazy s A ∧
        (∑ σ,law.val σ*expectedCost A s (List.ofFn σ))≤
          competitiveMultiplier*(1+Real.log ((k:ℝ)+1))^2*
            (∑ σ,law.val σ*optimalCost s (List.ofFn σ))+D:=by
  refine ⟨max (inventory Y k R L) 0,le_max_right _ _,?_⟩
  intro H law
  have hr:∀ d:Fin L,0<radii R L d:=fun d=>div_pos hR (by positivity)
  obtain ⟨A,hA,hcost⟩:=cost_by_keys s law hk hR hL hdia hf
  refine ⟨A,hA,?_⟩
  have hK:=JointEmbedding.key_bound s law hr hR (by norm_num : (2:ℝ)≤32) (fun d=>rfl)
  have he:=embedding_coefficient hk
  have ho:=opt_nonneg s law
  have hell:=ActualCaps.ell_ge_one hk
  have hm:=constants_pos.2.2.2.1
  have hn:=constants_pos.2.2.2.2.1
  have hc:=mul_le_mul_of_nonneg_right he ho
  have hfinal:=mul_le_mul_of_nonneg_left (hK.trans (add_le_add hc (le_refl _)))
    (mul_nonneg hm.le (by linarith : 0≤ActualCaps.ell k))
  have hpow:optMultiplier*ActualCaps.ell k*EmbeddedCost.opt s law≤
      optMultiplier*(ActualCaps.ell k)^2*EmbeddedCost.opt s law:=by
    have hsq:ActualCaps.ell k≤(ActualCaps.ell k)^2:=by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hn.le) ho
  have hi:=le_max_left (inventory Y k R L) 0
  change _≤competitiveMultiplier*(ActualCaps.ell k)^2*EmbeddedCost.opt s law+max (inventory Y k R L) 0
  dsimp only [inventory,competitiveMultiplier,embeddingInventory] at hi ⊢
  nlinarith [hcost,hfinal,hpow,hi]
end KServer.GlobalEndpoint

end


/-! Every finite metric admits a finite geometric prefix depth; no discreteness
assumption is introduced at the arbitrary-metric endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
attribute [local instance] Classical.propDecidable Classical.decEq

lemma finite_scales (Y:Type*) [MetricSpace Y] [Fintype Y]:
    ∃ R:ℝ,0<R ∧ ∃ L:ℕ,0<L ∧ (∀ x y:Y,dist x y≤R) ∧
      (∀ x y:Y,dist x y≤20*(R/(32:ℝ)^L)→x=y):=by
  let S:ℝ:=∑ x:Y,∑ y:Y,dist x y
  let I:ℝ:=∑ x:Y,∑ y:Y,(dist x y)⁻¹
  have hS:0≤S:=sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>dist_nonneg))
  have hI:0≤I:=sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>inv_nonneg.mpr dist_nonneg))
  let R:=S+1
  have hR:0<R:=by dsimp [R]; linarith
  have hdia:∀ x y:Y,dist x y≤R:=by
    intro x y
    have h1:dist x y≤∑ z:Y,dist x z:=single_le_sum (f:=fun z:Y=>dist x z) (fun _ _=>dist_nonneg) (mem_univ y)
    have h2:(∑ z:Y,dist x z)≤S:=single_le_sum (f:=fun a:Y=>∑ z:Y,dist a z)
      (fun _ _=>sum_nonneg (fun _ _=>dist_nonneg)) (mem_univ x)
    dsimp only [R]
    linarith
  let ε:=1/(I+1)
  have hε:0<ε:=one_div_pos.mpr (by linarith)
  have hsep:∀ x y:Y,x≠y→ε<dist x y:=by
    intro x y hne
    have hp:0<dist x y:=dist_pos.mpr hne
    have h1:(dist x y)⁻¹≤∑ z:Y,(dist x z)⁻¹:=single_le_sum (f:=fun z:Y=>(dist x z)⁻¹)
      (fun _ _=>inv_nonneg.mpr dist_nonneg) (mem_univ y)
    have h2:(∑ z:Y,(dist x z)⁻¹)≤I:=single_le_sum (f:=fun a:Y=>∑ z:Y,(dist a z)⁻¹)
      (fun _ _=>sum_nonneg (fun _ _=>inv_nonneg.mpr dist_nonneg)) (mem_univ x)
    apply (one_div_lt (by linarith : 0<I+1) hp).mpr
    rw [one_div]
    linarith
  obtain ⟨n,hn⟩:=exists_pow_lt_of_lt_one (div_pos hε (by positivity : 0<20*R))
    (show (1/32:ℝ)<1 by norm_num)
  have hl:20*(R/(32:ℝ)^(n+1))<ε:=by
    have hp:(1/32:ℝ)^(n+1)≤(1/32:ℝ)^n:=by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
    have hh:=hp.trans_lt hn
    rw [one_div_pow] at hh
    have hh':=(lt_div_iff₀ (show 0<20*R by positivity)).mp hh
    calc
      20*(R/(32:ℝ)^(n+1))=(1/(32:ℝ)^(n+1))*(20*R):=by ring
      _<ε:=hh'
  refine ⟨R,hR,n+1,by omega,hdia,?_⟩
  intro x y hxy
  by_contra hne
  exact (not_lt_of_ge hxy) (hl.trans (hsep x y hne))
end KServer.GlobalEndpoint

end

end OAI

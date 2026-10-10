import Mathlib
import OAI.Probability.ParisiFinite.SpinWZeroApply

namespace OAI

/-! Spin Coe Add. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

@[simp] theorem spinCoe_add (x y : PreSpin E) : spinCoe (x+y)=spinCoe x+spinCoe y := by
  ext i
  simp only [spinCoe_apply,Pi.add_apply,UniformSpace.Completion.coe_add,PiLp.add_apply]

@[simp] theorem spinCoe_zero : spinCoe (0:PreSpin E)=0 := by
  ext i
  simp only [spinCoe_apply,Pi.zero_apply,UniformSpace.Completion.coe_zero,PiLp.zero_apply]

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem spinMass_add (x y : PreSpin E) : spinMass (x+y)≤ spinMass x+spinMass y := by
  unfold spinMass
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => mass_add_le (x i) (y i))

def preSpinW (d : E) (x : PreSpin E) : PreSpin E := fun i => preWLinear d (x i)

@[simp] theorem spinCoe_preSpinW (d : E) (x : PreSpin E) :
    spinCoe (preSpinW d x)=spinW d (spinCoe x) := by
  ext i
  simp only [spinCoe_apply,preSpinW,spinW_apply,W_coe]

theorem spinMass_preSpinW (d : E) (x : PreSpin E) : spinMass (preSpinW d x)≤ spinMass x :=
  Finset.sum_le_sum (fun i _ => mass_preW_le d (x i))

theorem SpinRadiusLE.preSpinW {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B) (d : E) :
    SpinRadiusLE (preSpinW d x) (‖d‖+B) := fun i => (hx i).preW d

namespace BoundedPacket

theorem zero : BoundedPacket l (fun _ : α => (0:SpinSpace E)) := by
  refine ⟨fun _ => 0,0,0,le_rfl,le_rfl,fun _ => spinCoe_zero.symm,?_⟩
  exact Eventually.of_forall fun _ => ⟨fun _ => RadiusLE.zero _,by simp [spinMass,mass]⟩

theorem add {x y : α → SpinSpace E} (hx : BoundedPacket l x) (hy : BoundedPacket l y) :
    BoundedPacket l (fun q => x q+y q) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  obtain ⟨p',B',A',hB',hA',hp',hbound'⟩ := hy
  refine ⟨fun q => p q+p' q,max B B',A+A',le_max_of_le_left hB,add_nonneg hA hA',?_,?_⟩
  · exact fun q => by simp only [spinCoe_add,hp,hp']
  · filter_upwards [hbound,hbound'] with q hq hq'
    exact ⟨fun i => ((hq.1 i).mono (le_max_left _ _)).add ((hq'.1 i).mono (le_max_right _ _)),
      (spinMass_add _ _).trans (add_le_add hq.2 hq'.2)⟩

theorem sum {ι : Type*} (s : Finset ι) (x : ι → α → SpinSpace E)
    (hx : ∀i∈s,BoundedPacket l (x i)) : BoundedPacket l (fun q => ∑i∈s,x i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero (E:=E) (α:=α) (l:=l))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hx i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

theorem weyl {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (d : α → E) (C : ℝ) (hC : 0≤C) (hd : ∀ᶠ q in l,‖d q‖≤C) :
    BoundedPacket l (fun q => spinW (d q) (x q)) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  refine ⟨fun q => preSpinW (d q) (p q),C+B,A,add_nonneg hC hB,hA,?_,?_⟩
  · exact fun q => by simp only [spinCoe_preSpinW,hp]
  · filter_upwards [hbound,hd] with q hq hdq
    exact ⟨fun i => (hq.1.preSpinW (d q) i).mono (by linarith),
      (spinMass_preSpinW _ _).trans hq.2⟩

end BoundedPacket
end CoherentFock

 

open scoped InnerProductSpace Topology BigOperators
namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def spinSector (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun j => if j=i then 1 else 0)
def projectSpin (i : Fin 2) : SpinSpace E →L[ℂ] SpinSpace E := SpinOperators.act (spinSector i)
def signedMode (i : Fin 2) (d : E) : E := if i=0 then d else -d

@[simp] theorem projectSpin_apply (i j : Fin 2) (x : SpinSpace E) :
    projectSpin i x j=if j=i then x j else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [projectSpin,spinSector,SpinOperators.act_apply,Matrix.diagonal]

@[simp] theorem projectSpin_sum (x : SpinSpace E) : ∑i : Fin 2,projectSpin i x=x := by
  ext j
  simp only [Fin.sum_univ_two,PiLp.add_apply,projectSpin_apply]
  fin_cases j <;> simp

@[simp] theorem spinW_project (d : E) (i : Fin 2) (x : SpinSpace E) :
    spinW d (projectSpin i x)=projectSpin i (spinW d x) := spinW_root _ _ _

@[simp] theorem projectSpin_projectSpin (i : Fin 2) (x : SpinSpace E) :
    projectSpin i (projectSpin i x)=projectSpin i x := by
  ext j
  simp only [projectSpin_apply]
  split_ifs <;> rfl

omit [InnerProductSpace ℂ E] in
@[simp] theorem norm_signedMode (i : Fin 2) (d : E) : ‖signedMode i d‖=‖d‖ := by
  unfold signedMode
  split_ifs <;> simp

 theorem WZ_project (d : E) (i : Fin 2) (x : SpinSpace E) :
    WZ d (projectSpin i x)=spinW (signedMode i d) (projectSpin i x) := by
  ext j
  simp only [WZ_apply,spinW_apply,projectSpin_apply]
  by_cases hj : j=i
  · subst j; simp only [ite_true]; rfl
  · simp only [hj,ite_false,map_zero]

 theorem spinW_mul_apply (d e : E) (x : SpinSpace E) :
    spinW d (spinW e x)=phase d e • spinW (d+e) x := by
  ext i
  simpa only [ContinuousLinearMap.comp_apply,smul_apply,spinW_apply,PiLp.smul_apply]
    using congrArg (fun T : Space E →L[ℂ] Space E => T (x i)) (W_mul d e)

 theorem spinW_add_split (d e : E) (x : SpinSpace E) :
    spinW (d+e) x=(phase d e)⁻¹ • spinW d (spinW e x) := by
  rw [spinW_mul_apply,smul_smul,inv_mul_cancel₀,one_smul]
  exact norm_ne_zero_iff.mp (by rw [norm_phase]; norm_num)

omit [InnerProductSpace ℂ E] in
 theorem signedMode_add (i : Fin 2) (d e : E) :
    signedMode i (d+e)=signedMode i d+signedMode i e := by
  unfold signedMode
  split_ifs <;> abel

 theorem WZ_sector_split (d e : E) (x : SpinSpace E) :
    WZ (d+e) x=∑i : Fin 2, (phase (signedMode i d) (signedMode i e))⁻¹ •
      spinW (signedMode i d) (spinW (signedMode i e) (projectSpin i x)) := by
  conv_lhs => rw [←projectSpin_sum x,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [WZ_project,signedMode_add,spinW_add_split]

 

 theorem rotated_WZ_sector_split (A : Matrix (Fin 2) (Fin 2) ℂ) (d e : E) (x : SpinSpace E) :
    SpinOperators.act A (WZ (d+e) x)=
      ∑i : Fin 2,∑j : Fin 2,spinW (signedMode i d)
        ((phase (signedMode i d) (signedMode i e))⁻¹ •
          projectSpin j (SpinOperators.act A (spinW (signedMode i e) (projectSpin i x)))) := by
  rw [WZ_sector_split,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul]
  rw [←Finset.smul_sum,←map_sum,projectSpin_sum,spinW_root]

namespace BoundedPacket
open Filter
variable {α : Type*} {l : Filter α}

 theorem project {x : α → SpinSpace E} (hx : BoundedPacket l x) (i : Fin 2) :
    BoundedPacket l (fun q => projectSpin i (x q)) := hx.root (spinSector i)

 theorem rotated_sector_tail {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (d e : α → E) (C : ℝ) (hC : 0≤C)
    (he : ∀ᶠ q in l,‖e q‖≤C) (i j : Fin 2) :
    BoundedPacket l (fun q => (phase (signedMode i (d q)) (signedMode i (e q)))⁻¹ •
      projectSpin j (SpinOperators.act A (spinW (signedMode i (e q)) (projectSpin i (x q))))) := by
  apply ((((hx.project i).weyl (fun q => signedMode i (e q)) C hC
    (by simpa only [norm_signedMode] using he)).root A).project j).smul _ 1 (by norm_num)
  exact Eventually.of_forall fun q => by simp only [norm_inv,norm_phase,inv_one,le_refl]

end BoundedPacket
end CoherentFock

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 theorem projectSpin_spinW (i : Fin 2) (d : E) (x : SpinSpace E) :
    projectSpin i (spinW d x)=spinW d (projectSpin i x) := (spinW_project _ _ _).symm

 theorem WZ_on_sector {i : Fin 2} {x : SpinSpace E} (hx : projectSpin i x=x) (d : E) :
    WZ d x=spinW (signedMode i d) x := by
  conv_lhs => rw [←hx]
  rw [WZ_project,hx]

 

 theorem WZ_packet_bounded {i : Fin 2} {x : SpinSpace E} (hx : projectSpin i x=x) (d c : E) :
    WZ d (spinW c x)=
      (phase (signedMode i d) c / phase c (signedMode i d)) •
        spinW c (spinW (signedMode i d) x) := by
  have hs : projectSpin i (spinW c x)=spinW c x := by rw [projectSpin_spinW,hx]
  rw [WZ_on_sector hs,spinW_mul_apply,spinW_mul_apply,smul_smul]
  rw [div_mul_cancel₀,add_comm c]
  exact norm_ne_zero_iff.mp (by rw [norm_phase]; norm_num)

 

 theorem WZ_packet_shift {i : Fin 2} {x : SpinSpace E} (hx : projectSpin i x=x) (d c : E) :
    WZ d (spinW c x)=phase (signedMode i d) c • spinW (c+signedMode i d) x := by
  have hs : projectSpin i (spinW c x)=spinW c x := by rw [projectSpin_spinW,hx]
  rw [WZ_on_sector hs,spinW_mul_apply,add_comm c]

 theorem rootX_sector (i : Fin 2) (x : SpinSpace E) :
    projectSpin (1-i) (SpinOperators.act RootSpin.X (projectSpin i x))=
      SpinOperators.act RootSpin.X (projectSpin i x) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [projectSpin_apply,SpinOperators.act_apply,RootSpin.X]

 theorem halfMixer_sector (i : Fin 2) (x : SpinSpace E) :
    projectSpin (1-i) (SpinOperators.act (RootSpin.R (Real.pi/2)) (projectSpin i x))=
      SpinOperators.act (RootSpin.R (Real.pi/2)) (projectSpin i x) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [projectSpin_apply,SpinOperators.act_apply,RootSpin.R,RootSpin.X,
      Real.cos_pi_div_two,Real.sin_pi_div_two]

namespace BoundedPacket
variable {α κ : Type*} [Fintype κ] {l : Filter α}

 

 theorem finite_uniform (x : κ → α → SpinSpace E) (hx : ∀i,BoundedPacket l (x i)) :
    ∃ (p : κ → α → PreSpin E) (B A : ℝ),0≤B ∧ 0≤A ∧
      (∀i q,x i q=spinCoe (p i q)) ∧
      (∀ᶠ q in l,∀i,SpinRadiusLE (p i q) B ∧ spinMass (p i q)≤A) := by
  classical
  choose p B A hB hA hp hbd using hx
  refine ⟨p,∑i,B i,∑i,A i,Finset.sum_nonneg (fun i _ => hB i),
    Finset.sum_nonneg (fun i _ => hA i),hp,?_⟩
  have hall : ∀ᶠ q in l,∀i,SpinRadiusLE (p i q) (B i) ∧ spinMass (p i q)≤A i :=
    eventually_all.mpr hbd
  filter_upwards [hall] with q hq i
  exact ⟨fun j => (hq i).1 j |>.mono (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)),
    (hq i).2.trans (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_univ i))⟩

 theorem cost_packet_tail {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (d c : α → E) (D : ℝ) (hD : 0≤D) (hd : ∀ᶠ q in l,‖d q‖≤D) (i : Fin 2) :
    BoundedPacket l (fun q => (phase (signedMode i (d q)) (c q) / phase (c q) (signedMode i (d q))) •
      spinW (signedMode i (d q)) (x q)) := by
  apply (hx.weyl (fun q => signedMode i (d q)) D hD
    (by simpa only [norm_signedMode] using hd)).smul _ 1 (by norm_num)
  exact Eventually.of_forall fun q => by simp only [norm_div,norm_phase,div_self one_ne_zero,le_refl]

end BoundedPacket
end CoherentFock

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

 

theorem low_insertion_scaled_bound
    (U : α → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E) (A : PacketUnitaryFamily (E:=E) l)
    (O Q : α → SpinSpace E →L[ℂ] SpinSpace E) (ζ : α → ℂ) (r S : α → ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _)
    (hscale : ∀ᶠ q in l,0≤r q ∧ 0≤S q ∧ S q*r q=1)
    (hsplit : ∀ᶠ q in l,∀x,U q x=O q x+Q q x)
    (hQ : ∀ᶠ q in l,∀x,‖Q q x‖≤r q*‖x‖)
    (hO : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖O q (x q)-ζ q • A.op q (x q)‖) l (𝓝 0)) :
    ∀ᶠ q in l,S q*‖(U q).symm (SpinOperators.act P (U q (PointedTree.vacuum E)))-
      (A.op q).symm (SpinOperators.act P (A.op q (PointedTree.vacuum E)))‖≤4 := by
  let Ω := PointedTree.vacuum E
  let test (q : α) := (A.op q).symm (SpinOperators.act P (A.op q Ω))
  let e₀ (q : α) := ‖O q Ω-ζ q • A.op q Ω‖
  let e₁ (q : α) := ‖O q (test q)-ζ q • A.op q (test q)‖
  have he : Tendsto (fun q => S q*(e₀ q+e₁ q)) l (𝓝 0) := by
    simpa only [e₀,e₁,test,Ω,mul_add,add_zero] using
      (hO (fun _ => Ω) BoundedPacket.vacuum).add (hO test (A.insertion_bounded P))
  filter_upwards [hscale,hsplit,hQ,he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with q hsq hsplitq hQq heq
  have hz : ∀x : SpinSpace E,‖SpinOperators.act P x‖≤‖x‖ :=
    fun x => (SpinOperators.norm_act hP x).le
  have hi := ForwardControl.insertion_split_bound (U q) (A.op q)
    (SpinOperators.act P) hz Ω (ζ q) (O q) (Q q) hsplitq (r q) (e₀ q+e₁ q)
    hsq.1 hQq (by dsimp only [e₀,e₁]; linarith [norm_nonneg (O q (test q)-ζ q • A.op q (test q))])
    (by dsimp only [e₀,e₁,test]; linarith [norm_nonneg (O q Ω-ζ q • A.op q Ω)])
  have hi' := mul_le_mul_of_nonneg_left hi hsq.2.1
  change S q*‖(U q).symm ((SpinOperators.act P) (U q Ω))-test q‖≤4
  dsimp only [Ω] at hi'
  rw [PointedTree.norm_vacuum] at hi'
  nlinarith [hsq.2.2]

 

theorem low_insertion_tendsto
    (U : α → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E) (A : PacketUnitaryFamily (E:=E) l)
    (O Q : α → SpinSpace E →L[ℂ] SpinSpace E) (ζ : α → ℂ) (r S : α → ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _)
    (hr : Tendsto r l (𝓝 0))
    (hscale : ∀ᶠ q in l,0≤r q ∧ 0≤S q ∧ S q*r q=1)
    (hsplit : ∀ᶠ q in l,∀x,U q x=O q x+Q q x)
    (hQ : ∀ᶠ q in l,∀x,‖Q q x‖≤r q*‖x‖)
    (hO : ∀x,BoundedPacket l x →
      Tendsto (fun q => S q*‖O q (x q)-ζ q • A.op q (x q)‖) l (𝓝 0)) :
    Tendsto (fun q => ‖(U q).symm (SpinOperators.act P (U q (PointedTree.vacuum E)))-
      (A.op q).symm (SpinOperators.act P (A.op q (PointedTree.vacuum E)))‖) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa only [mul_zero] using hr.const_mul 4)
  filter_upwards [hscale,low_insertion_scaled_bound U A O Q ζ r S P hP hscale hsplit hQ hO]
    with q hsq hi
  have hh := mul_le_mul_of_nonneg_left hi hsq.1
  rw [←mul_assoc,mul_comm (r q) (S q),hsq.2.2,one_mul] at hh
  simpa only [mul_comm] using hh

end CoherentFock

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
local instance initRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance initRealSMul : SMul ℝ ModeInfinity := initRealModule.toDistribMulAction.toSMul
local instance initRealSMulZero : SMulZeroClass ℝ ModeInfinity := { smul_zero := initRealModule.toDistribMulAction.smul_zero }

 

def eInfinity : ModeInfinity := insertionInfinity []
def vInfinity (b T : ℝ) : ModeInfinity :=
  insertionInfinity [.mixer (delta T),.cost (gamma b T)]
def highInfinity (γ : ℝ) : ModeInfinity := modeEmbed 3 (highDirection 2 γ)
def dInfinity (b T : ℝ) : ModeInfinity := (gamma b T : ℂ) • (vInfinity b T-eInfinity)
def wordInfinity (b T : ℝ) : List PointedTree.Gate :=
  PointedTree.initializationWord (gamma b T) (delta T) (Real.pi/4)

@[simp] theorem norm_eInfinity : ‖eInfinity‖=1 := norm_insertionInfinity []
@[simp] theorem norm_vInfinity (b T : ℝ) : ‖vInfinity b T‖=1 := norm_insertionInfinity _
@[simp] theorem norm_highInfinity (γ : ℝ) : ‖highInfinity γ‖=1 := by
  rw [highInfinity,(modeEmbed 3).norm_map,highDirection_norm]

theorem embed_initialDirection (n : ℕ) : modeEmbed n (initialDirection n)=eInfinity := by
  exact insertionInfinity_stable [] n (Nat.zero_le n)

theorem vInfinity_embed (b T : ℝ) :
    vInfinity b T=modeEmbed 3 (actualV 2 b T) := by
  exact (insertionInfinity_stable _ 3 (by simp)).symm

theorem vInfinity_eq (b T : ℝ) :
    vInfinity b T=(Real.cos (2*delta T):ℂ) • eInfinity+
      (Real.sin (2*delta T):ℂ) • highInfinity (gamma b T) := by
  rw [vInfinity_embed,actualV_eq,map_add,map_smul,map_smul,embed_initialDirection]
  rfl

@[simp] theorem modeFock_eInfinity : modeFock eInfinity=SpinOperators.act Z (vacuum ModeInfinity) := by
  rw [eInfinity,modeFock_insertion]
  apply (ordinaryLocal []).injective
  simp only [LinearIsometryEquiv.apply_symm_apply,ordinaryLocal_nil]

@[simp] theorem spinMap_vacuum {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (T : E →ₗᵢ[ℂ] F) :
    spinMap (gammaEmbedding T) (vacuum E)=vacuum F := by
  ext i
  simp only [spinMap_apply,vacuum_apply,map_smul,gammaEmbedding_coherent,map_zero]

theorem modeFock_highInfinity (γ : ℝ) :
    modeFock (highInfinity γ)=SpinOperators.act Y
      (WZ ((-2*γ:ℝ) • eInfinity) (vacuum ModeInfinity)) := by
  change unfoldTree (modeInWhole (modeEmbed 3 (highDirection 2 γ)))=_
  rw [modeInWhole_embed,unfoldTree_embed_succ]
  change spinMap (gammaEmbedding (modeEmbed 2)) (highDirection 2 γ : Level 3)=_
  rw [highDirection_coe,spinMap_root,spinMap_cost]
  change SpinOperators.act Y (WZ (modeEmbed 2 ((-2*γ:ℝ) • initialDirection 2))
    (spinMap (gammaEmbedding (modeEmbed 2)) (vacuum (Mode 2))))=_
  rw [spinMap_vacuum]
  have hm : modeEmbed 2 ((-2*γ:ℝ) • initialDirection 2)=(-2*γ:ℝ) • eInfinity := by
    calc
      _ = (-2*γ:ℝ) • modeEmbed 2 (initialDirection 2) := (modeEmbed 2).map_smul_of_tower _ _
      _ = _ := by rw [embed_initialDirection]
  rw [hm]

theorem initialMap_apply_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (γ δ β : ℝ) (v e : E) (x : SpinSpace E) :
    initialMap γ δ β v e x=SpinOperators.act (R β)
      (WZ ((γ:ℂ) • v) (SpinOperators.act (R δ) (WZ (-(γ:ℂ) • e) x))) := by
  simp only [initialMap_apply,←Complex.coe_smul,Complex.ofReal_neg]

@[simp] theorem ordinaryLocal_initialization (b T : ℝ) (x : SpinSpace ModeInfinity) :
    ordinaryLocal (wordInfinity b T) x=
      initialMap (gamma b T) (delta T) (Real.pi/4) (vInfinity b T) eInfinity x := by
  simp only [wordInfinity,PointedTree.initializationWord,ordinaryLocal_mixer,
    ordinaryLocal_cost,ordinaryLocal_nil,Complex.ofReal_neg,neg_neg,initialMap_apply_complex]
  rfl

theorem dInfinity_embed (b T : ℝ) :
    dInfinity b T=modeEmbed 3 (ordinaryDisplacement 2 b T) := by
  unfold dInfinity ordinaryDisplacement
  rw [←Complex.coe_smul,map_smul,map_sub,←vInfinity_embed,embed_initialDirection]

theorem dInfinity_bounded (b : ℝ) :
    ∀ᶠ T : ℝ in atTop,‖dInfinity b T‖≤2*|b|+1 := by
  simpa only [dInfinity_embed,(modeEmbed 3).norm_map] using ordinaryDisplacement_bounded 2 b

theorem dInfinity_approx_high (b : ℝ) :
    Tendsto (fun T => ‖dInfinity b T-(2*b:ℝ) • highInfinity (gamma b T)‖) atTop (𝓝 0) := by
  have he (T : ℝ) : dInfinity b T-(2*b:ℝ) • highInfinity (gamma b T)=
      modeEmbed 3 (ordinaryDisplacement 2 b T-(2*b:ℝ) • highDirection 2 (gamma b T)) := by
    rw [map_sub,←dInfinity_embed]
    congr 1
    exact ((modeEmbed 3).map_smul_of_tower (2*b:ℝ) (highDirection 2 (gamma b T))).symm
  simpa only [he,(modeEmbed 3).norm_map] using tendsto_ordinaryDisplacement_error 2 b

 
def lowInfinity (b : ℝ) : PacketUnitaryFamily (E:=ModeInfinity) (atTop : Filter ℝ) :=
  (PacketUnitaryFamily.pulse (dInfinity b) (2*|b|+1) (by positivity)
    (dInfinity_bounded b)).trans (PacketUnitaryFamily.root (R (Real.pi/4)) (R_unitary _))

@[simp] theorem lowInfinity_apply (b T : ℝ) (x : SpinSpace ModeInfinity) :
    (lowInfinity b).op T x=
      ordinaryMap (gamma b T) (Real.pi/4) (vInfinity b T) eInfinity x := rfl

def phaseInfinity (b T : ℝ) : ℂ :=
  phase (gamma b T • vInfinity b T) ((-gamma b T) • eInfinity)

def ordinaryPartInfinity (b T : ℝ) : SpinSpace ModeInfinity →L[ℂ] SpinSpace ModeInfinity :=
  ordinaryCoefficient (gamma b T) (delta T) (vInfinity b T) eInfinity •
    (ordinaryMap (gamma b T) (Real.pi/4) (vInfinity b T) eInfinity).toContinuousLinearEquiv.toContinuousLinearMap

def specialPartInfinity (b T : ℝ) : SpinSpace ModeInfinity →L[ℂ] SpinSpace ModeInfinity :=
  specialCoefficient (gamma b T) (delta T) (vInfinity b T) eInfinity •
    (specialMap (gamma b T) (Real.pi/4) (vInfinity b T) eInfinity).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem ordinaryPartInfinity_apply (b T : ℝ) (x : SpinSpace ModeInfinity) :
    ordinaryPartInfinity b T x=ordinaryCoefficient (gamma b T) (delta T) (vInfinity b T) eInfinity •
      ordinaryMap (gamma b T) (Real.pi/4) (vInfinity b T) eInfinity x := rfl

@[simp] theorem specialPartInfinity_apply (b T : ℝ) (x : SpinSpace ModeInfinity) :
    specialPartInfinity b T x=specialCoefficient (gamma b T) (delta T) (vInfinity b T) eInfinity •
      specialMap (gamma b T) (Real.pi/4) (vInfinity b T) eInfinity x := rfl

@[simp] theorem norm_phaseInfinity (b T : ℝ) : ‖phaseInfinity b T‖=1 := norm_phase _ _

theorem exact_splitInfinity (b T : ℝ) (x : SpinSpace ModeInfinity) :
    ordinaryLocal (wordInfinity b T) x=ordinaryPartInfinity b T x+specialPartInfinity b T x := by
  rw [ordinaryLocal_initialization]
  exact exact_split _ _ _ _ _ _

theorem norm_specialPartInfinity (b : ℝ) {T : ℝ} (hT : 1≤T) (x : SpinSpace ModeInfinity) :
    ‖specialPartInfinity b T x‖=amplitude T*‖x‖ := by
  change ‖specialCoefficient _ _ _ _ • specialMap _ _ _ _ x‖=_
  rw [norm_special_component,sin_delta hT,abs_of_pos (amplitude_pos hT)]

theorem lowInfinity_accuracy (b : ℝ) (x : ℝ → SpinSpace ModeInfinity)
    (hx : BoundedPacket atTop x) :
    Tendsto (fun T => T*‖ordinaryPartInfinity b T (x T)-phaseInfinity b T •
      (lowInfinity b).op T (x T)‖) atTop (𝓝 0) := by
  obtain ⟨C,hC,hxC⟩ := hx.norm_bounded
  apply squeeze_zero' _ _ (by simpa only [zero_mul] using tendsto_amplitude.mul_const C)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact mul_nonneg (by linarith) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (1:ℝ),hxC] with T hT hxT
    have hh := ordinary_component_error (gamma b T) (Real.pi/4) hT (vInfinity b T) eInfinity (x T)
    have hh' : ‖ordinaryPartInfinity b T (x T)-phaseInfinity b T • (lowInfinity b).op T (x T)‖≤
        (amplitude T)^2*‖x T‖ := by
      rw [ordinaryPartInfinity_apply,lowInfinity_apply]
      exact hh
    have hT0 : 0≤T := by linarith
    calc
      _ ≤ T*((amplitude T)^2*‖x T‖) := mul_le_mul_of_nonneg_left hh' hT0
      _ ≤ T*((amplitude T)^2*C) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxT (sq_nonneg _)) hT0
      _ = amplitude T*C := by
        unfold amplitude
        field_simp

 

theorem highInfinity_escapes (b : ℝ) (hb : 0<b) (x : ℝ → SpinSpace ModeInfinity)
    (hx : BoundedPacket atTop x) :
    Tendsto (fun T => ⟪x T,modeFock (highInfinity (gamma b T))⟫_ℂ) atTop (𝓝 0) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  simp only [hp,modeFock_highInfinity]
  exact tendsto_inner_spinCoe_rootY_uniform _ p
    (tendsto_norm_scaled_unit (gamma b) (fun _ => eInfinity) (tendsto_gamma b hb)
      (fun _ => norm_eInfinity)) B A hB hbound

end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
local instance packetRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance packetRealSMul : SMul ℝ ModeInfinity := packetRealModule.toDistribMulAction.toSMul
local instance packetRealSMulZero : SMulZeroClass ℝ ModeInfinity := { smul_zero := packetRealModule.toDistribMulAction.smul_zero }

 theorem signedMode_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) (i : Fin 2) (d : E) : signedMode i (c • d)=c • signedMode i d := by
  unfold signedMode
  split_ifs <;> simp only [smul_neg]

 theorem specialCoefficient_eq (γ δ : ℝ) (v e : ModeInfinity) :
    specialCoefficient γ δ v e=(Real.sin δ:ℂ)*specialPhase γ v e := by
  unfold specialCoefficient specialPhase
  ring

 theorem special_displacement (γ : ℝ) (v e : ModeInfinity) :
    (-γ:ℝ) • (v+e)=((-2*γ:ℝ):ℂ) • e + -((γ:ℂ) • (v-e)) := by
  rw [←Complex.coe_smul]
  push_cast
  module

 theorem specialPart_expanded (b T : ℝ) (x : SpinSpace ModeInfinity) :
    specialPartInfinity b T x=(Real.sin (delta T):ℂ) •
      (specialPhase (gamma b T) (vInfinity b T) eInfinity •
        SpinOperators.act (R (Real.pi/4)*X)
          (WZ (((-2*gamma b T:ℝ):ℂ) • eInfinity + -dInfinity b T) x)) := by
  rw [specialPartInfinity_apply,specialCoefficient_eq,specialMap_apply,smul_smul]
  rw [special_displacement,SpinOperators.act_mul,ContinuousLinearMap.comp_apply]
  rfl

 
def initialCenter (b : ℝ) (i : Fin 2) : ModeInfinity :=
  signedMode i ((-2*b:ℝ) • eInfinity)

def initialTail (b T : ℝ) (i j : Fin 2) (x : SpinSpace ModeInfinity) : SpinSpace ModeInfinity :=
  specialPhase (gamma b T) (vInfinity b T) eInfinity •
    ((phase (signedMode i ((-2*gamma b T:ℝ) • eInfinity)) (signedMode i (-dInfinity b T)))⁻¹ •
      projectSpin j (SpinOperators.act (R (Real.pi/4)*X)
        (spinW (signedMode i (-dInfinity b T)) (projectSpin i x))))

 theorem initialCenter_scale (b T : ℝ) (i : Fin 2) :
    signedMode i ((-2*gamma b T:ℝ) • eInfinity)=(T:ℂ) • initialCenter b i := by
  simp only [initialCenter,←Complex.coe_smul,←signedMode_smul,smul_smul,gamma]
  congr 2
  push_cast
  ring

 theorem initial_special_packets (b : ℝ) {T : ℝ} (hT : 1≤T) (x : SpinSpace ModeInfinity) :
    specialPartInfinity b T x=(amplitude T:ℂ) •
      ∑i : Fin 2,∑j : Fin 2,spinW ((T:ℂ) • initialCenter b i) (initialTail b T i j x) := by
  rw [specialPart_expanded,sin_delta hT]
  congr 1
  rw [Complex.coe_smul,rotated_WZ_sector_split,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [initialTail,initialCenter_scale,map_smul]

 theorem initialTail_bounded (b : ℝ) (x : ℝ → SpinSpace ModeInfinity)
    (hx : BoundedPacket atTop x) (i j : Fin 2) :
    BoundedPacket atTop (fun T => initialTail b T i j (x T)) := by
  apply (hx.rotated_sector_tail (R (Real.pi/4)*X)
    (fun T => (-2*gamma b T:ℝ) • eInfinity) (fun T => -dInfinity b T)
    (2*|b|+1) (by positivity)
    (by simpa only [norm_neg] using dInfinity_bounded b) i j).smul _ 1 (by norm_num)
  exact Eventually.of_forall fun T => (norm_specialPhase _ _ _).le

 theorem initialTail_sector (b T : ℝ) (i j : Fin 2) (x : SpinSpace ModeInfinity) :
    projectSpin j (initialTail b T i j x)=initialTail b T i j x := by
  simp only [initialTail,map_smul,projectSpin_projectSpin]

 theorem norm_initialCenter (b : ℝ) (i : Fin 2) : ‖initialCenter b i‖=2*|b| := by
  rw [initialCenter,norm_signedMode,norm_smul,norm_eInfinity,mul_one,Real.norm_eq_abs]
  rw [abs_mul]
  norm_num

end SeedInitialization

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype κ]
  {l : Filter α}

 

def PacketExpansion (S r : α → ℝ) (d : κ → α → E) (spin : κ → Fin 2)
    (u : α → SpinSpace E) : Prop :=
  ∃ τ : κ → α → SpinSpace E,
    (∀i,BoundedPacket l (τ i)) ∧
    (∀i q,projectSpin (spin i) (τ i q)=τ i q) ∧
    Tendsto (fun q => S q*‖u q-∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q)‖) l (𝓝 0)

namespace PacketExpansion
variable {S r : α → ℝ} {d : κ → α → E} {spin : κ → Fin 2} {u v : α → SpinSpace E}

 theorem close (hu : PacketExpansion (l:=l) S r d spin u)
    (hS : ∀ᶠ q in l,0≤S q)
    (hv : Tendsto (fun q => S q*‖v q-u q‖) l (𝓝 0)) :
    PacketExpansion (l:=l) S r d spin v := by
  obtain ⟨τ,hτ,hspin,he⟩ := hu
  refine ⟨τ,hτ,hspin,?_⟩
  apply squeeze_zero' _ _ (by simpa only [add_zero,mul_add] using hv.add he)
  · filter_upwards [hS] with q hq
    exact mul_nonneg hq (norm_nonneg _)
  · filter_upwards [hS] with q hq
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub (v q) (u q) (∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q))) hq

 theorem bounded_cost (hu : PacketExpansion (l:=l) S r d spin u)
    (c : α → E) (C : ℝ) (hC : 0≤C) (hc : ∀ᶠ q in l,‖c q‖≤C) :
    PacketExpansion (l:=l) S r d spin (fun q => WZ (c q) (u q)) := by
  obtain ⟨τ,hτ,hspin,he⟩ := hu
  let τ' (i : κ) (q : α) :=
    (phase (signedMode (spin i) (c q)) ((S q:ℂ) • d i q) /
      phase ((S q:ℂ) • d i q) (signedMode (spin i) (c q))) •
      spinW (signedMode (spin i) (c q)) (τ i q)
  refine ⟨τ',fun i => (hτ i).cost_packet_tail c (fun q => (S q:ℂ) • d i q) C hC hc (spin i),?_,?_⟩
  · intro i q
    simp only [τ',map_smul,projectSpin_spinW,hspin]
  · have hsum (q : α) : WZ (c q) (∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q))=
        ∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ' i q) := by
      simp only [map_sum,map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [WZ_packet_bounded (hspin i q)]
      simp only [τ',map_smul]
    simpa only [←hsum,←map_sub,norm_WZ] using he

 theorem huge_cost (hu : PacketExpansion (l:=l) S r d spin u) (c : α → E) :
    PacketExpansion (l:=l) S r (fun i q => d i q+signedMode (spin i) (c q)) spin
      (fun q => WZ ((S q:ℂ) • c q) (u q)) := by
  obtain ⟨τ,hτ,hspin,he⟩ := hu
  let τ' (i : κ) (q : α) :=
    phase (signedMode (spin i) ((S q:ℂ) • c q)) ((S q:ℂ) • d i q) • τ i q
  refine ⟨τ',?_,?_,?_⟩
  · intro i
    exact (hτ i).smul _ 1 (by norm_num) (Eventually.of_forall fun _ => (norm_phase _ _).le)
  · intro i q
    simp only [τ',map_smul,hspin]
  · have hsum (q : α) : WZ ((S q:ℂ) • c q) (∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q))=
        ∑i,(r q:ℂ) • spinW ((S q:ℂ) • (d i q+signedMode (spin i) (c q))) (τ' i q) := by
      simp only [map_sum,map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [WZ_packet_shift (hspin i q)]
      simp only [τ',map_smul,smul_add,SeedInitialization.signedMode_smul]
    simpa only [←hsum,←map_sub,norm_WZ] using he

 theorem half_mixer (hu : PacketExpansion (l:=l) S r d spin u) :
    PacketExpansion (l:=l) S r d (fun i => 1-spin i)
      (fun q => SpinOperators.act (RootSpin.R (Real.pi/2)) (u q)) := by
  obtain ⟨τ,hτ,hspin,he⟩ := hu
  let A := RootSpin.R (Real.pi/2)
  refine ⟨fun i q => SpinOperators.act A (τ i q),fun i => (hτ i).root A,?_,?_⟩
  · intro i q
    change projectSpin (1-spin i) (SpinOperators.act (RootSpin.R (Real.pi/2)) (τ i q))=_
    conv_lhs => rw [←hspin i q]
    rw [halfMixer_sector,hspin]
  · have hsum (q : α) : SpinOperators.act A (∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q))=
        ∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (SpinOperators.act A (τ i q)) := by
      simp only [map_sum,map_smul,spinW_root]
    simpa only [←hsum,A,←map_sub,SpinOperators.norm_act (RootSpin.R_unitary _)] using he

end PacketExpansion
end CoherentFock

end

end OAI

import Mathlib
import OAI.Probability.ParisiFinite.HugeSelectiveBounded

namespace OAI

/-! Insertion Approx. -/

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
namespace PointedTree
open CoherentFock RootSpin
local instance apRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance apRealSMul : SMul ℝ ModeInfinity := apRealModule.toDistribMulAction.toSMul
namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r S : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

theorem insertion_approx (st : PacketStage l r S d spin) (hr : Tendsto r l (𝓝 0))
    (hscale : ∀ᶠ q in l,0≤r q ∧ 0≤S q ∧ S q*r q=1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) :
    ApproxPacket l (fun q => (ordinaryLocal (st.word q)).symm
      (SpinOperators.act P (ordinaryLocal (st.word q) (vacuum ModeInfinity)))) := by
  refine ⟨fun q => (st.low.op q).symm (SpinOperators.act P (st.low.op q (vacuum ModeInfinity))),
    st.low.insertion_bounded P,?_⟩
  exact low_insertion_tendsto _ st.low st.ordinary st.special st.phase r S P hP hr hscale
    (Eventually.of_forall st.split) (st.special_norm.mono fun _ hq x => (hq x).le) st.ordinary_low

theorem insertionZ_approx (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q) :
    ApproxPacket l (fun q => modeFock (insertionInfinity (st.word q))) := by
  simpa only [modeFock_insertion] using st.insertion_approx hr
    (hp.mono fun q hq => ⟨hq.le,(inv_pos.mpr hq).le,inv_mul_cancel₀ hq.ne'⟩) Z Z_unitary

theorem insertionY_approx (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q) :
    ApproxPacket l (fun q => modeFock (insertionYInfinity (st.word q))) := by
  simpa only [modeFock_insertionY] using st.insertion_approx hr
    (hp.mono fun q hq => ⟨hq.le,(inv_pos.mpr hq).le,inv_mul_cancel₀ hq.ne'⟩) Y Y_unitary

 

theorem huge_transverse_approx (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (ht : t≠0) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (v : α → ModeInfinity) (hv : ApproxPacket l (fun q => modeFock (v q))) :
    Tendsto (fun q => ⟪insertionYInfinity (st.forwardWord t q),v q⟫_ℂ) l (𝓝 0) := by
  obtain ⟨η,hη,he⟩ := hv
  have hh := st.huge_transverse_bounded t ht hr hp η hη
  have herr : Tendsto (fun q => ⟪modeFock (insertionYInfinity (st.forwardWord t q)),modeFock (v q)⟫_ℂ-
      ⟪modeFock (insertionYInfinity (st.forwardWord t q)),η q⟫_ℂ) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ he
    exact Eventually.of_forall fun q => by
      rw [←inner_sub_right]
      have hn : ‖modeFock (insertionYInfinity (st.forwardWord t q))‖=1 := by
        rw [modeFock.norm_map,insertionYInfinity,norm_insertionInfinity]
      simpa only [hn,one_mul] using norm_inner_le_norm (𝕜:=ℂ)
        (modeFock (insertionYInfinity (st.forwardWord t q))) (modeFock (v q)-η q)
  simpa only [sub_add_cancel,add_zero,modeFock.inner_map_map] using herr.add hh

theorem forwardCenter_approx (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (hr : Tendsto r l (𝓝 0)) (hp : ∀ᶠ q in l,0<r q)
    (hd : ∀i,ApproxPacket l (fun q => modeFock (d i q))) (i : κ) :
    ApproxPacket l (fun q => modeFock (st.forwardCenter t i q)) := by
  have he (v : ModeInfinity) : modeFock ((-t) • v)=(((-t):ℝ):ℂ) • modeFock v := by
    change modeFock ((((-t):ℝ):ℂ) • v)=_
    exact map_smul _ _ _
  have hv := (st.insertionZ_approx hr hp).smul ((-t:ℝ):ℂ)
  unfold forwardCenter signedMode
  split_ifs
  · simpa only [map_add,he] using (hd i).add hv
  · simpa only [map_add,map_neg,he] using (hd i).add hv.neg

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}

 
def combination (d : ι → E) (c : ι → ℂ) : E := ∑i,c i • d i

theorem combination_add (d : ι → E) (a b : ι → ℂ) :
    combination d (a+b)=combination d a+combination d b := by
  simp only [combination,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem combination_neg (d : ι → E) (a : ι → ℂ) :
    combination d (-a)=-combination d a := by
  simp only [combination,Pi.neg_apply,neg_smul,Finset.sum_neg_distrib]

theorem combination_smul (d : ι → E) (z : ℂ) (a : ι → ℂ) :
    combination d (z • a)=z • combination d a := by
  simp only [combination,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

@[simp] theorem combination_zero (d : ι → E) : combination d 0=0 := by
  simp [combination]

def GramConverges (l : Filter α) (d : α → ι → E) (d₀ : ι → F) : Prop :=
  ∀i j,Tendsto (fun q => ⟪d q i,d q j⟫_ℂ) l (𝓝 ⟪d₀ i,d₀ j⟫_ℂ)

namespace GramConverges
variable {d : α → ι → E} {d₀ : ι → F}

theorem combinations (hg : GramConverges l d d₀) (a b : ι → ℂ) :
    Tendsto (fun q => ⟪combination (d q) a,combination (d q) b⟫_ℂ)
      l (𝓝 ⟪combination d₀ a,combination d₀ b⟫_ℂ) := by
  simp only [combination,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((hg j i).const_mul (star (a j))).const_mul (b i)

theorem phase (hg : GramConverges l d d₀) (a b : ι → ℂ) :
    Tendsto (fun q => CoherentFock.phase (combination (d q) a) (combination (d q) b))
      l (𝓝 (CoherentFock.phase (combination d₀ a) (combination d₀ b))) := by
  have hi := (Complex.continuous_im.tendsto _).comp (hg.combinations a b)
  have hr := (Complex.continuous_ofReal.tendsto _).comp hi.neg
  exact (Complex.continuous_exp.tendsto _).comp (hr.mul_const Complex.I)

 

theorem norm_combination (hg : GramConverges l d d₀) (a : ι → ℂ) :
    Tendsto (fun q => ‖combination (d q) a‖) l (𝓝 ‖combination d₀ a‖) := by
  have hh := tendsto_norm_sq_of_inner (fun q => combination (d q) a) (combination d₀ a)
    (hg.combinations a a)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm] using hs

theorem combination_bounded (hg : GramConverges l d d₀) (a : ι → ℂ) :
    ∀ᶠ q in l,‖combination (d q) a‖≤‖combination d₀ a‖+1 := by
  exact ((hg.norm_combination a).eventually
    (gt_mem_nhds (by linarith : ‖combination d₀ a‖<‖combination d₀ a‖+1))).mono fun _ h => h.le

end GramConverges

 
theorem spinPacket_reindex {κ ν : Type*} [Fintype κ] [Fintype ν]
    (e : κ ≃ ν) (a : ν → Fin 2 → ℂ) (d : ν → E) :
    spinPacket (fun i => a (e i)) (fun i => d (e i))=spinPacket a d := by
  ext q
  simp only [spinPacket_apply]
  exact e.sum_comp (fun i => a i q • coherent (d i))

end GramCalculus

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock PointedTree
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}

 

def PacketMatch (l : Filter α) (d : α → ι → E) (d₀ : ι → F)
    (x : α → SpinSpace E) (x₀ : SpinSpace F) : Prop :=
  ∃ (n : ℕ) (a : α → Fin n → Fin 2 → ℂ) (a₀ : Fin n → Fin 2 → ℂ) (c : Fin n → ι → ℂ),
    (∀q,x q=spinPacket (a q) (fun i => combination (d q) (c i))) ∧
    x₀=spinPacket a₀ (fun i => combination d₀ (c i)) ∧
    (∀i j,Tendsto (fun q => a q i j) l (𝓝 (a₀ i j)))

namespace PacketMatch
variable {d : α → ι → E} {d₀ : ι → F} {x y : α → SpinSpace E} {x₀ y₀ : SpinSpace F}

theorem vacuum : PacketMatch l d d₀ (fun _ => PointedTree.vacuum E) (PointedTree.vacuum F) := by
  refine ⟨1,fun _ _ _ => spinCoefficient,fun _ _ => spinCoefficient,fun _ => 0,?_,?_,?_⟩
  · intro q; ext i; simp [spinPacket_apply,vacuum_apply,spinCoefficient]
  · ext i; simp [spinPacket_apply,vacuum_apply,spinCoefficient]
  · exact fun _ _ => tendsto_const_nhds

theorem root (hx : PacketMatch l d d₀ x x₀) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    PacketMatch l d d₀ (fun q => SpinOperators.act P (x q)) (SpinOperators.act P x₀) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  refine ⟨n,fun t i q => ∑j,P q j*a t i j,fun i q => ∑j,P q j*a₀ i j,c,?_,?_,?_⟩
  · intro q; dsimp only; rw [hx,act_spinPacket]
  · rw [hx₀,act_spinPacket]
  · intro i q
    exact tendsto_finsetSum _ fun j _ => (ha i j).const_mul (P q j)

theorem smul (hx : PacketMatch l d d₀ x x₀) (z : ℂ) :
    PacketMatch l d d₀ (fun q => z • x q) (z • x₀) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  refine ⟨n,fun t i q => z*a t i q,fun i q => z*a₀ i q,c,?_,?_,?_⟩
  · intro q; dsimp only; rw [hx,spinPacket_smul]
  · rw [hx₀,spinPacket_smul]
  · exact fun i q => (ha i q).const_mul z

 

theorem pulse (hg : GramConverges l d d₀) (hx : PacketMatch l d d₀ x x₀) (b : ι → ℂ) :
    PacketMatch l d d₀ (fun q => WZ (combination (d q) b) (x q)) (WZ (combination d₀ b) x₀) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  let e : Fin (n*2) ≃ Fin n × Fin 2 := finProdFinEquiv.symm
  let bc (p : Fin n × Fin 2) : ι → ℂ := if p.2=0 then b else -b
  have hbE (q : α) (p : Fin n × Fin 2) : combination (d q) (bc p)=
      if p.2=0 then combination (d q) b else -combination (d q) b := by
    dsimp only [bc]; split_ifs <;> simp only [combination_neg]
  have hbF (p : Fin n × Fin 2) : combination d₀ (bc p)=
      if p.2=0 then combination d₀ b else -combination d₀ b := by
    dsimp only [bc]; split_ifs <;> simp only [combination_neg]
  let aa (q : α) (p : Fin n × Fin 2) (j : Fin 2) : ℂ :=
    if j=p.2 then phase (combination (d q) (bc p)) (combination (d q) (c p.1))*a q p.1 j else 0
  let aa₀ (p : Fin n × Fin 2) (j : Fin 2) : ℂ :=
    if j=p.2 then phase (combination d₀ (bc p)) (combination d₀ (c p.1))*a₀ p.1 j else 0
  refine ⟨n*2,fun q i => aa q (e i),fun i => aa₀ (e i),fun i => bc (e i)+c (e i).1,?_,?_,?_⟩
  · intro q
    simp only [combination_add]
    rw [spinPacket_reindex e (aa q) (fun p => combination (d q) (bc p)+combination (d q) (c p.1))]
    simp only [aa,hbE,hx q,WZ_spinPacket]
  · simp only [combination_add]
    rw [spinPacket_reindex e aa₀ (fun p => combination d₀ (bc p)+combination d₀ (c p.1))]
    simp only [aa₀,hbF,hx₀,WZ_spinPacket]
  · intro i j
    dsimp only [aa,aa₀]
    split_ifs
    · exact (hg.phase (bc (e i)) (c (e i).1)).mul (ha (e i).1 j)
    · exact tendsto_const_nhds

 

theorem inner (hx : PacketMatch l d d₀ x x₀) (hy : PacketMatch l d d₀ y y₀)
    (hg : GramConverges l d d₀) :
    Tendsto (fun q => ⟪x q,y q⟫_ℂ) l (𝓝 ⟪x₀,y₀⟫_ℂ) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  obtain ⟨m,b,b₀,e,hy,hy₀,hb⟩ := hy
  simp only [hx,hy,hx₀,hy₀]
  exact tendsto_inner_spinPacket a b (fun q i => combination (d q) (c i))
    (fun q i => combination (d q) (e i)) a₀ b₀ (fun i => combination d₀ (c i))
    (fun i => combination d₀ (e i)) ha hb
    (fun i => hg.combinations (c i) (c i)) (fun i => hg.combinations (e i) (e i))
    (fun i j => hg.combinations (c i) (e j))

 

theorem creation (hx : PacketMatch l d d₀ x x₀) (hg : GramConverges l d d₀)
    (h : α → E) (h₀ : F)
    (hcol : ∀i,Tendsto (fun q => ⟪d q i,h q⟫_ℂ) l (𝓝 ⟪d₀ i,h₀⟫_ℂ)) :
    Tendsto (fun q => ⟪x q,plusEmbedding (creationVacuum (h q))⟫_ℂ)
      l (𝓝 ⟪x₀,plusEmbedding (creationVacuum h₀)⟫_ℂ) := by
  obtain ⟨n,a,a₀,c,hx,hx₀,ha⟩ := hx
  simp only [hx,hx₀]
  apply tendsto_inner_spinPacket_creation a (fun q i => combination (d q) (c i)) h a₀
    (fun i => combination d₀ (c i)) h₀ ha (fun i => hg.combinations (c i) (c i))
  intro i
  simp only [combination,sum_inner,inner_smul_left]
  exact tendsto_finsetSum _ fun j _ => (hcol j).const_mul (star (c i j))

end PacketMatch
end GramCalculus

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock PointedTree
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}

namespace PacketMatch
variable {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E} {x₀ : SpinSpace F}

theorem norm (hx : PacketMatch l d d₀ x x₀) (hg : GramConverges l d d₀) :
    Tendsto (fun q => ‖x q‖) l (𝓝 ‖x₀‖) := by
  have h := tendsto_norm_sq_of_inner x x₀ (hx.inner hx hg)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm] using hs

end PacketMatch

 

def ApproxMatch (l : Filter α) (d : α → ι → E) (d₀ : ι → F)
    (x : α → SpinSpace E) (x₀ : SpinSpace F) : Prop :=
  ∃y,PacketMatch l d d₀ y x₀ ∧ Tendsto (fun q => ‖x q-y q‖) l (𝓝 0)

theorem PacketMatch.approx {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E} {x₀ : SpinSpace F}
    (hx : PacketMatch l d d₀ x x₀) : ApproxMatch l d d₀ x x₀ :=
  ⟨x,hx,by simpa only [sub_self,norm_zero] using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))⟩

namespace ApproxMatch
variable {d : α → ι → E} {d₀ : ι → F} {x y : α → SpinSpace E} {x₀ y₀ : SpinSpace F}

theorem close (hy : ApproxMatch l d d₀ y x₀)
    (he : Tendsto (fun q => ‖x q-y q‖) l (𝓝 0)) : ApproxMatch l d d₀ x x₀ := by
  obtain ⟨z,hz,hyz⟩ := hy
  refine ⟨z,hz,?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [add_zero] using he.add hyz)
  exact Eventually.of_forall fun q => by simpa only [dist_eq_norm] using dist_triangle (x q) (y q) (z q)

theorem norm (hx : ApproxMatch l d d₀ x x₀) (hg : GramConverges l d d₀) :
    Tendsto (fun q => ‖x q‖) l (𝓝 ‖x₀‖) := by
  obtain ⟨y,hy,he⟩ := hx
  have hdiff : Tendsto (fun q => ‖x q‖-‖y q‖) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ he
    exact Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x q) (y q)
  simpa only [sub_add_cancel,zero_add] using hdiff.add (hy.norm hg)

theorem norm_bounded (hx : ApproxMatch l d d₀ x x₀) (hg : GramConverges l d d₀) :
    ∀ᶠ q in l,‖x q‖≤‖x₀‖+1 :=
  ((hx.norm hg).eventually (gt_mem_nhds (by linarith : ‖x₀‖<‖x₀‖+1))).mono fun _ h => h.le

 

theorem inner (hx : ApproxMatch l d d₀ x x₀) (hy : ApproxMatch l d d₀ y y₀)
    (hg : GramConverges l d d₀) :
    Tendsto (fun q => ⟪x q,y q⟫_ℂ) l (𝓝 ⟪x₀,y₀⟫_ℂ) := by
  obtain ⟨x',hx',he⟩ := hx
  obtain ⟨y',hy',hf⟩ := hy
  have hdiff : Tendsto (fun q => ⟪x q,y q⟫_ℂ-⟪x' q,y' q⟫_ℂ) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun q => ?_)
      (show Tendsto (fun q => ‖x q-x' q‖*‖y q‖+‖x' q‖*‖y q-y' q‖) l (𝓝 0) from by
        simpa only [zero_mul,mul_zero,add_zero] using
          (he.mul ((show ApproxMatch l d d₀ y y₀ from ⟨y',hy',hf⟩).norm hg)).add ((hx'.norm hg).mul hf))
    have hsplit : ⟪x q,y q⟫_ℂ-⟪x' q,y' q⟫_ℂ=
        ⟪x q-x' q,y q⟫_ℂ+⟪x' q,y q-y' q⟫_ℂ := by simp only [inner_sub_left,inner_sub_right]; ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
  simpa only [sub_add_cancel,zero_add] using hdiff.add (hx'.inner hy' hg)

 

theorem creation (hx : ApproxMatch l d d₀ x x₀) (hg : GramConverges l d d₀)
    (h : α → E) (h₀ : F)
    (hcol : ∀i,Tendsto (fun q => ⟪d q i,h q⟫_ℂ) l (𝓝 ⟪d₀ i,h₀⟫_ℂ))
    (hnorm : Tendsto (fun q => ‖h q‖) l (𝓝 ‖h₀‖)) :
    Tendsto (fun q => ⟪x q,plusEmbedding (creationVacuum (h q))⟫_ℂ)
      l (𝓝 ⟪x₀,plusEmbedding (creationVacuum h₀)⟫_ℂ) := by
  obtain ⟨y,hy,he⟩ := hx
  have hdiff : Tendsto (fun q => ⟪x q,plusEmbedding (creationVacuum (h q))⟫_ℂ-
      ⟪y q,plusEmbedding (creationVacuum (h q))⟫_ℂ) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa only [zero_mul] using he.mul hnorm)
    exact Eventually.of_forall fun q => by
      rw [←inner_sub_left]
      simpa only [plusEmbedding.norm_map,norm_creationVacuum] using
        norm_inner_le_norm (𝕜:=ℂ) (x q-y q) (plusEmbedding (creationVacuum (h q)))
  simpa only [sub_add_cancel,zero_add] using hdiff.add (hy.creation hg h h₀ hcol)

end ApproxMatch
end GramCalculus

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace GramCalculus
open CoherentFock PointedTree

 

inductive WeylGate (ι : Type*) where
  | root (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _)
  | pulse (c : ι → ℂ)

namespace WeylGate
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}

def op (d : ι → E) : WeylGate ι → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E
  | .root P hP => SpinOperators.actEquiv P hP
  | .pulse c => costEquiv (combination d c)

def inv : WeylGate ι → WeylGate ι
  | .root P hP => .root P.conjTranspose (root_adjoint_unitary P hP)
  | .pulse c => .pulse (-c)

@[simp] theorem op_inv (d : ι → E) (g : WeylGate ι) : op d g.inv=(op d g).symm := by
  cases g with
  | root P hP => apply LinearIsometryEquiv.ext; intro x; exact (SpinOperators.actEquiv_symm_apply P hP x).symm
  | pulse c => apply LinearIsometryEquiv.ext; intro x; simp only [inv,op,costEquiv_apply,costEquiv_symm_apply,combination_neg]

theorem packet_match {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E} {x₀ : SpinSpace F}
    (g : WeylGate ι) (hx : PacketMatch l d d₀ x x₀) (hg : GramConverges l d d₀) :
    PacketMatch l d d₀ (fun q => op (d q) g (x q)) (op d₀ g x₀) := by
  cases g with
  | root P hP => exact hx.root P
  | pulse c => exact hx.pulse hg c

theorem bounded {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E}
    (g : WeylGate ι) (hx : BoundedPacket l x) (hg : GramConverges l d d₀) :
    BoundedPacket l (fun q => op (d q) g (x q)) := by
  cases g with
  | root P hP => exact hx.root P
  | pulse c => exact hx.pulse _ (‖combination d₀ c‖+1) (by positivity) (hg.combination_bounded c)

end WeylGate

namespace WeylWord
variable {E F α ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] {l : Filter α}

def op (d : ι → E) : List (WeylGate ι) → SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E
  | [] => LinearIsometryEquiv.refl ℂ _
  | g::w => (op d w).trans (g.op d)

@[simp] theorem op_nil (d : ι → E) : op d []=LinearIsometryEquiv.refl ℂ _ := rfl
@[simp] theorem op_cons (d : ι → E) (g : WeylGate ι) (w : List (WeylGate ι)) (x : SpinSpace E) :
    op d (g::w) x=g.op d (op d w x) := rfl

@[simp] theorem op_append (d : ι → E) (u w : List (WeylGate ι)) (x : SpinSpace E) :
    op d (u++w) x=op d u (op d w x) := by
  induction u with
  | nil => rfl
  | cons g u ih => simp only [List.cons_append,op_cons,ih]

def inv (w : List (WeylGate ι)) : List (WeylGate ι) := w.reverse.map WeylGate.inv

@[simp] theorem op_inv (d : ι → E) (w : List (WeylGate ι)) : op d (inv w)=(op d w).symm := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    apply LinearIsometryEquiv.ext
    intro x
    simp only [inv,List.reverse_cons,List.map_append,List.map_singleton,op_append,op_cons,
      op_nil,WeylGate.op_inv]
    change op d (inv w) ((g.op d).symm x)=(op d w).symm ((g.op d).symm x)
    rw [ih]

theorem packet_match {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E} {x₀ : SpinSpace F}
    (w : List (WeylGate ι)) (hx : PacketMatch l d d₀ x x₀) (hg : GramConverges l d d₀) :
    PacketMatch l d d₀ (fun q => op (d q) w (x q)) (op d₀ w x₀) := by
  induction w with
  | nil => exact hx
  | cons g w ih => exact g.packet_match ih hg

theorem bounded {d : α → ι → E} {d₀ : ι → F} {x : α → SpinSpace E}
    (w : List (WeylGate ι)) (hx : BoundedPacket l x) (hg : GramConverges l d d₀) :
    BoundedPacket l (fun q => op (d q) w (x q)) := by
  induction w with
  | nil => exact hx
  | cons g w ih => exact g.bounded ih hg

 

theorem insertion_match {d : α → ι → E} {d₀ : ι → F}
    (w : List (WeylGate ι)) (P : Matrix (Fin 2) (Fin 2) ℂ) (hg : GramConverges l d d₀) :
    PacketMatch l d d₀
      (fun q => (op (d q) w).symm (SpinOperators.act P (op (d q) w (vacuum E))))
      ((op d₀ w).symm (SpinOperators.act P (op d₀ w (vacuum F)))) := by
  simpa only [op_inv] using packet_match (inv w) ((packet_match w PacketMatch.vacuum hg).root P) hg

end WeylWord
end GramCalculus

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : Filter α}

 

theorem BoundedPacket.pulse_close {x : α → SpinSpace E} (hx : BoundedPacket l x)
    (d e : α → E) (C : ℝ) (he : ∀ᶠ q in l,‖e q‖≤C)
    (hd : Tendsto (fun q => ‖d q-e q‖) l (𝓝 0)) :
    Tendsto (fun q => ‖WZ (d q) (x q)-WZ (e q) (x q)‖) l (𝓝 0) := by
  obtain ⟨p,B,A,hB,hA,hp,hbound⟩ := hx
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [zero_mul] using hd.mul_const (A*(1+2*B+12*B^2)+C*A))
  filter_upwards [hbound,he] with q hq heq
  rw [hp]
  exact WZ_spinCoe_difference (d q) (e q) (p q) hq.1 hB hq.2 heq

namespace PacketUnitaryFamily

 

def LowClose (A B : PacketUnitaryFamily (E:=E) l) : Prop :=
  ∀x,BoundedPacket l x → Tendsto (fun q => ‖A.op q (x q)-B.op q (x q)‖) l (𝓝 0)

namespace LowClose
variable {A B C D : PacketUnitaryFamily (E:=E) l}

theorem refl (A : PacketUnitaryFamily (E:=E) l) : LowClose A A := by
  intro x hx
  simpa only [sub_self,norm_zero] using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))

theorem symm (h : LowClose A B) : LowClose B A := by
  intro x hx
  simpa only [norm_sub_rev] using h x hx

theorem trans (h : LowClose A B) (h' : LowClose B C) : LowClose A C := by
  intro x hx
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [add_zero] using (h x hx).add (h' x hx))
  exact Eventually.of_forall fun q => norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem comp (h : LowClose A B) (h' : LowClose C D) :
    LowClose (A.trans C) (B.trans D) := by
  intro x hx
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [add_zero] using (h x hx).add (h' _ (B.forward x hx)))
  exact Eventually.of_forall fun q => by
    change ‖C.op q (A.op q (x q))-D.op q (B.op q (x q))‖≤_
    have he := norm_sub_le_norm_sub_add_norm_sub (C.op q (A.op q (x q)))
      (C.op q (B.op q (x q))) (D.op q (B.op q (x q)))
    simpa only [←map_sub,(C.op q).norm_map] using he

theorem inverse (h : LowClose A B) : LowClose A.symm B.symm := by
  intro x hx
  have hh := h (fun q => (B.op q).symm (x q)) (B.backward x hx)
  apply hh.congr
  intro q
  symm
  change ‖(A.op q).symm (x q)-(B.op q).symm (x q)‖=_
  rw [←(A.op q).norm_map,map_sub,(A.op q).apply_symm_apply,(B.op q).apply_symm_apply,norm_sub_rev]

theorem insertion (h : LowClose A B) (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P ∈ unitary _) :
    Tendsto (fun q => ‖(A.op q).symm (SpinOperators.act P (A.op q (PointedTree.vacuum E)))-
      (B.op q).symm (SpinOperators.act P (B.op q (PointedTree.vacuum E)))‖) l (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [add_zero] using (h _ BoundedPacket.vacuum).add (h _ (B.insertion_bounded P)))
  exact Eventually.of_forall fun q => by
    simpa only [one_smul] using ForwardControl.insertion_from_forward (A.op q) (B.op q)
      (SpinOperators.act P) (fun x => (SpinOperators.norm_act hP x).le) (PointedTree.vacuum E) (1:ℂ)

end LowClose

theorem pulse_lowClose (d e : α → E) (D C : ℝ) (hD : 0≤D) (hC : 0≤C)
    (hd : ∀ᶠ q in l,‖d q‖≤D) (he : ∀ᶠ q in l,‖e q‖≤C)
    (herr : Tendsto (fun q => ‖d q-e q‖) l (𝓝 0)) :
    LowClose (pulse d D hD hd) (pulse e C hC he) := by
  intro x hx
  exact hx.pulse_close d e C he herr

end PacketUnitaryFamily
end CoherentFock

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace PointedTree
open CoherentFock RootSpin
local instance htrRealModule : Module ℝ ModeInfinity := (inferInstance : NormedSpace ℝ ModeInfinity).toModule
local instance htrRealSMul : SMul ℝ ModeInfinity := htrRealModule.toDistribMulAction.toSMul

namespace PacketStage
variable {α κ : Type*} [Fintype κ] {l : Filter α} {r : α → ℝ}
  {d : κ → α → ModeInfinity} {spin : κ → Fin 2}

theorem halfEcho_transport_exact (st : PacketStage l r (fun q => (r q)⁻¹) d spin)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (q : α) (x : SpinSpace ModeInfinity) :
    (ordinaryLocal (st.halfEchoWord t a K q)).symm
      (SpinOperators.act Z (st.halfEchoGain t a K q x))=
    (ordinaryLocal (st.forwardWord t q)).symm ((probeGain (r q) (st.forwardWord t q) a K).symm
      (SpinOperators.act Z (probeGain (r q) (st.forwardWord t q) a K (WZ (st.forwardVector t q) x)))) := by
  rw [halfEchoGain_apply]
  have he := cost_transport_exact (probePrefix (r q) (st.forwardWord t q) a K) (-(t/r q))
    (probeGain (r q) (st.forwardWord t q) a K (WZ (st.forwardVector t q) x))
  simp only [Complex.ofReal_neg,neg_neg,Complex.coe_smul] at he
  change (ordinaryLocal (.cost (-(t/r q))::probePrefix (r q) (st.forwardWord t q) a K)).symm
    (SpinOperators.act Z (WZ ((t/r q) • insertionInfinity (probePrefix (r q) (st.forwardWord t q) a K))
      (probeGain (r q) (st.forwardWord t q) a K (WZ (st.forwardVector t q) x))))=_
  rw [he]
  apply local_symm_after_gain
  exact probeGain_on_local _ _ _ _

 

theorem Transported.halfEcho {st : PacketStage l r (fun q => (r q)⁻¹) d spin}
    {address : α → SpinSpace ModeInfinity} (ht : st.Transported address)
    (t : ℝ) (a : ℕ → ShortPulse) (K : ℕ) (G : ℝ) (hG : 0≤G)
    (hg : ∀ᶠ q in l,‖st.halfEchoResidual t a K q‖≤G) (hp : ∀ᶠ q in l,0<r q)
    (ho : ∀x,BoundedPacket l x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K
        (WZ (st.forwardVector t q) (x q))-WZ (st.forwardVector t q) (x q)‖) l (𝓝 0))
    (hs : ∀x,PacketExpansion (l:=l) (fun q => (r q)⁻¹) r (st.forwardCenter t) spin x →
      Tendsto (fun q => (r q)⁻¹*‖probeGain (r q) (st.forwardWord t q) a K (x q)-
        SpinOperators.act (R (Real.pi/2)) (x q)‖) l (𝓝 0)) :
    (st.halfEcho t a K G hG hg hp ho (fun x hx => hs _ (st.forward_special_packets t x hx))).Transported
      (fun q => -address q) := by
  let s (q : α) := WZ (st.forwardVector t q) (st.special q (vacuum ModeInfinity))
  have hpack := st.forward_special_packets t _ BoundedPacket.vacuum
  have h1 := hs _ hpack
  have h2 := hs _ hpack.rootZ
  have ht' : Tendsto (fun q => ‖(((r q)⁻¹:ℝ):ℂ) • (ordinaryLocal (st.forwardWord t q)).symm
      (SpinOperators.act Z (s q))-address q‖) l (𝓝 0) := by
    have he (q : α) : (ordinaryLocal (st.forwardWord t q)).symm (SpinOperators.act Z (s q))=
        (ordinaryLocal (st.word q)).symm (SpinOperators.act Z (st.special q (vacuum ModeInfinity))) := by
      simpa only [s,forwardWord,forwardVector,complex_neg_real_smul] using
        cost_transport_exact (st.word q) (t/r q) (st.special q (vacuum ModeInfinity))
    simpa only [he,Transported] using ht
  have hh := ForwardControl.scaled_special_transport (fun q => ordinaryLocal (st.forwardWord t q))
    (fun q => probeGain (r q) (st.forwardWord t q) a K) (SpinOperators.act Z)
    (SpinOperators.act (R (Real.pi/2)))
    (fun x : SpinSpace ModeInfinity => (SpinOperators.norm_act Z_unitary x).le)
    half_mixer_anticommutes s address (fun q => (r q)⁻¹)
    (hp.mono fun _ hq => (inv_pos.mpr hq).le) h1 h2 ht'
  change Tendsto (fun q => ‖(((r q)⁻¹:ℝ):ℂ) • (ordinaryLocal (st.halfEchoWord t a K q)).symm
    (SpinOperators.act Z (st.halfEchoGain t a K q (st.special q (vacuum ModeInfinity))))-(-address q)‖) l (𝓝 0)
  simpa only [halfEcho_transport_exact,sub_neg_eq_add,s] using hh

end PacketStage
end PointedTree

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace CoherentFock
open RootSpin
variable {E α κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype κ]
  {l : Filter α}

theorem negativeHalfMixer_sector (i : Fin 2) (x : SpinSpace E) :
    projectSpin (1-i) (SpinOperators.act (R (-(Real.pi/2))) (projectSpin i x))=
      SpinOperators.act (R (-(Real.pi/2))) (projectSpin i x) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [projectSpin_apply,SpinOperators.act_apply,R,
      Real.cos_pi_div_two,Real.sin_pi_div_two,X]

theorem negative_half_mixer_anticommutes (x : SpinSpace E) :
    SpinOperators.act Z (SpinOperators.act (R (-(Real.pi/2))) x)=
      -SpinOperators.act (R (-(Real.pi/2))) (SpinOperators.act Z x) := by
  ext i
  fin_cases i <;>
    simp [SpinOperators.act_apply,Fin.sum_univ_two,R,Z,X,
      Real.cos_pi_div_two,Real.sin_pi_div_two]

theorem PacketExpansion.negative_half_mixer {r S : α → ℝ} {d : κ → α → E}
    {spin : κ → Fin 2} {u : α → SpinSpace E} (hu : PacketExpansion (l:=l) S r d spin u) :
    PacketExpansion (l:=l) S r d (fun i => 1-spin i)
      (fun q => SpinOperators.act (RootSpin.R (-(Real.pi/2))) (u q)) := by
  obtain ⟨τ,hτ,hspin,he⟩ := hu
  let A := RootSpin.R (-(Real.pi/2))
  refine ⟨fun i q => SpinOperators.act A (τ i q),fun i => (hτ i).root A,?_,?_⟩
  · intro i q
    change projectSpin (1-spin i) (SpinOperators.act (RootSpin.R (-(Real.pi/2))) (τ i q))=_
    conv_lhs => rw [←hspin i q]
    rw [negativeHalfMixer_sector,hspin]
  · have hsum (q : α) : SpinOperators.act A (∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (τ i q))=
        ∑i,(r q:ℂ) • spinW ((S q:ℂ) • d i q) (SpinOperators.act A (τ i q)) := by
      simp only [map_sum,map_smul,spinW_root]
    simpa only [←hsum,A,←map_sub,SpinOperators.norm_act (RootSpin.R_unitary _)] using he

end CoherentFock

end

end OAI

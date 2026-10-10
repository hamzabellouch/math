import Mathlib
import OAI.Combinatorics.StripMass.FluxWindow

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

def bandVertices (H : ℕ) (v : Vertex) : Prop := 0≤v.2.1 ∧ v.2.1<(H:ℤ)

def stripPort (H : ℕ) : ℤ⊕ℤ→State
  | .inl j=>bottom j
  | .inr j=>top H j

lemma stripPort_injective (H : ℕ) : Function.Injective (stripPort H) := by
  rintro (j|j) (k|k) he <;> simp [stripPort,bottom,top] at he ⊢ <;> tauto

lemma stripPort_inside (H : ℕ) (hH : 1≤H) (b : ℤ⊕ℤ) : bandVertices H (stripPort H b).1 := by
  cases b <;> dsimp [stripPort,bandVertices,bottom,top] <;> omega

lemma stripPort_outside (H : ℕ) (_hH : 1≤H) (b : ℤ⊕ℤ) : ¬bandVertices H (back (stripPort H b)).1 := by
  cases b <;> simp [stripPort,bandVertices,bottom,top,back,neighbor]

lemma stripPort_complete (H : ℕ) (s : State) (hi : bandVertices H s.1)
    (ho : ¬bandVertices H (back s).1) : ∃b,stripPort H b=s := by
  rcases s with ⟨⟨k,r,b⟩,p⟩
  fin_cases p
  · cases b
    · refine ⟨.inr k,?_⟩
      dsimp [bandVertices,back,neighbor] at hi ho
      have hr : r=(H:ℤ)-1 := by omega
      simp [stripPort,top,hr]
    · refine ⟨.inl k,?_⟩
      dsimp [bandVertices,back,neighbor] at hi ho
      have hr : r=0 := by omega
      simp [stripPort,bottom,hr]
  · cases b <;> simp [bandVertices,back,neighbor] at hi ho <;> omega
  · cases b <;> simp [bandVertices,back,neighbor] at hi ho <;> omega

def stripBoundaryPorts (H : ℕ) (hH : 1≤H) : BoundaryPorts (bandVertices H) (ℤ⊕ℤ) where
  port:=stripPort H
  injective:=stripPort_injective H
  inside:=stripPort_inside H hH
  outside:=stripPort_outside H hH
  complete:=stripPort_complete H

abbrev StepEndpoint := ℤ⊕(ℤ⊕Unit)

def stepPort (N : ℕ) (s : ℤ) : StepEndpoint→State
  | .inl j=>bottom j
  | .inr (.inl j)=>stepTop N s j
  | .inr (.inr _)=>sidePort N s

lemma stepPort_injective (N : ℕ) (s : ℤ) : Function.Injective (stepPort N s) := by
  rintro (j|(j|u)) (k|(k|v)) he
  all_goals simp only [stepPort,stepTop] at he
  all_goals try split_ifs at he
  all_goals simp_all [bottom,top,sidePort]

lemma stepPort_inside (N : ℕ) (hN : 1≤N) (s : ℤ) (b : StepEndpoint) :
    steppedVertices N s (stepPort N s b).1 := by
  rcases b with j|(j|u)
  · dsimp [stepPort,steppedVertices,bottom]; omega
  · simp only [stepPort,stepTop]
    split_ifs <;> dsimp [steppedVertices,top] <;> omega
  · dsimp [stepPort,steppedVertices,sidePort]; omega

lemma stepPort_outside (N : ℕ) (_hN : 1≤N) (s : ℤ) (b : StepEndpoint) :
    ¬steppedVertices N s (back (stepPort N s b)).1 := by
  rcases b with j|(j|u)
  · simp [stepPort,back,bottom,neighbor,steppedVertices]
  · simp only [stepPort,stepTop]
    split_ifs <;> dsimp [steppedVertices,top,back,neighbor] <;> omega
  · dsimp [stepPort,steppedVertices,sidePort,back,neighbor]; omega

lemma stepPort_complete (N : ℕ) (s : ℤ) (x : State) (hi : steppedVertices N s x.1)
    (ho : ¬steppedVertices N s (back x).1) : ∃b,stepPort N s b=x := by
  rcases x with ⟨⟨k,r,b⟩,p⟩
  fin_cases p
  · cases b
    · refine ⟨.inr (.inl k),?_⟩
      dsimp [steppedVertices,back,neighbor] at hi ho
      by_cases hk : k<s
      · have hr : r=(N:ℤ)-1 := by omega
        simp [stepPort,stepTop,hk,top,hr]
      · have hr : r=(N:ℤ) := by omega
        simp [stepPort,stepTop,hk,top,hr]
    · refine ⟨.inl k,?_⟩
      dsimp [steppedVertices,back,neighbor] at hi ho
      have hr : r=0 := by omega
      simp [stepPort,bottom,hr]
  · cases b
    · dsimp [steppedVertices,back,neighbor] at hi ho; omega
    · refine ⟨.inr (.inr ()),?_⟩
      dsimp [steppedVertices,back,neighbor] at hi ho
      have hr : r=(N:ℤ) := by omega
      have hk : k=s := by omega
      simp [stepPort,sidePort,hr,hk]
  · cases b <;> dsimp [steppedVertices,back,neighbor] at hi ho <;> omega

def stepBoundaryPorts (N : ℕ) (hN : 1≤N) (s : ℤ) : BoundaryPorts (steppedVertices N s) StepEndpoint where
  port:=stepPort N s
  injective:=stepPort_injective N s
  inside:=stepPort_inside N hN s
  outside:=stepPort_outside N hN s
  complete:=stepPort_complete N s

lemma retract_bottom (j : ℤ) : retractVertex (bottom j).1=up j 0 := rfl
lemma retract_top (H : ℕ) (hH : 1≤H) (j : ℤ) : retractVertex (top H j).1=down j (H-1) := by
  dsimp [retractVertex,top,down]
  congr 2
  omega
lemma retract_side (N : ℕ) (s : ℤ) : retractVertex (sidePort N s).1=up s N := by
  simp [retractVertex,sidePort,up]

lemma boundaryPathWeight_strip_bottom (H : ℕ) (hH : 1≤H) (i j : ℤ) (p : List Triangle) :
    boundaryPathWeight (stripBoundaryPorts H hH) H i (.inl j,p)=betweenArchWeight H i j p := by
  have hc : ValidBoundaryPath (stripBoundaryPorts H hH) H i (.inl j,p) ↔
      i≠j ∧ PathBetween H (up i 0) (up j 0) p := by
    simp only [ValidBoundaryPath,stripBoundaryPorts,stripPort,retract_bottom]
    have hb : bottom i≠bottom j ↔ i≠j := by simp [bottom]
    rw [hb]
    constructor
    · rintro ⟨h,hp,_⟩; exact ⟨h,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨h,hp,fun v hv=>⟨by simp [embedTriangle],by change (v.2.1:ℤ)<(H:ℤ); exact_mod_cast hp.2.2.2.2 v hv⟩⟩
  simp only [boundaryPathWeight,betweenArchWeight,hc]

def betweenBridgeWeight (H : ℕ) (i j : ℤ) (p : List Triangle) : ℝ :=
  if 0<H ∧ PathBetween H (up i 0) (down j (H-1)) p then rho^p.length else 0

lemma betweenBridgeWeight_nonneg (H : ℕ) (i j : ℤ) (p : List Triangle) :
    0≤betweenBridgeWeight H i j p := by
  unfold betweenBridgeWeight
  split_ifs <;> positivity [rho_pos]

lemma betweenBridgeWeight_translate (H : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenBridgeWeight H i j (p.map (translateTriangle i))=bridgeWeight H (j-i) p := by
  have hi : up i 0=translateTriangle i (up 0 0) := by simp
  have hj : down j (H-1)=translateTriangle i (down (j-i) (H-1)) := by simp
  simp only [betweenBridgeWeight,bridgeWeight,hi,hj,pathBetween_translate_iff,pathBetween_source,List.length_map]

lemma betweenBridgeWeight_summable (H : ℕ) (hH : 1≤H) (i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>betweenBridgeWeight H i x.1 x.2) := by
  have hf:=stripSumsFinite hH
  have hi (j : ℤ) : Summable (betweenBridgeWeight H i j) := by
    rw [←(translatePaths i).summable_iff]
    apply (hf.2.1 (j-i)).congr
    intro p
    exact (betweenBridgeWeight_translate H i j p).symm
  have he (j : ℤ) : (∑'p,betweenBridgeWeight H i j p)=bridgeKernel H (j-i) := by
    rw [←(translatePaths i).tsum_eq]
    exact tsum_congr (betweenBridgeWeight_translate H i j)
  apply (summable_prod_of_nonneg (fun x=>betweenBridgeWeight_nonneg H i x.1 x.2)).mpr
  refine ⟨hi,?_⟩
  simp_rw [he]
  exact hf.2.2.2.1.comp_injective (i:=fun j : ℤ=>j-i) (by intro a b hh; dsimp at hh; omega)

lemma betweenArchWeight_summable (H : ℕ) (hH : 1≤H) (i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>betweenArchWeight H i x.1 x.2) := by
  have hf:=stripSumsFinite hH
  apply (summable_prod_of_nonneg (fun x=>betweenArchWeight_nonneg H i x.1 x.2)).mpr
  refine ⟨fun j=>(summable_betweenArchWeight_iff H i j).mpr (hf.1 _),?_⟩
  change Summable (fun j=>betweenArchKernel H i j)
  simp_rw [betweenArchKernel_eq]
  exact hf.2.2.1.comp_injective (i:=fun j : ℤ=>j-i) (by intro a b hh; dsimp at hh; omega)

lemma boundaryPathWeight_strip_top (H : ℕ) (hH : 1≤H) (i j : ℤ) (p : List Triangle) :
    boundaryPathWeight (stripBoundaryPorts H hH) H i (.inr j,p)=betweenBridgeWeight H i j p := by
  have hc : ValidBoundaryPath (stripBoundaryPorts H hH) H i (.inr j,p) ↔
      0<H ∧ PathBetween H (up i 0) (down j (H-1)) p := by
    simp only [ValidBoundaryPath,stripBoundaryPorts,stripPort,retract_top H hH]
    have hb : bottom i≠top H j := by simp [bottom,top]
    change (bottom i≠top H j ∧ PathBetween H (up i 0) (down j (H-1)) p ∧ _) ↔ _
    rw [and_iff_right hb]
    constructor
    · rintro ⟨hp,_⟩; exact ⟨by omega,hp⟩
    · rintro ⟨_,hp⟩
      exact ⟨hp,fun v hv=>⟨by simp [embedTriangle],by change (v.2.1:ℤ)<(H:ℤ); exact_mod_cast hp.2.2.2.2 v hv⟩⟩
  simp only [boundaryPathWeight,betweenBridgeWeight,hc]

lemma boundaryPathWeight_step_bottom (N : ℕ) (hN : 1≤N) (s i j : ℤ) (p : List Triangle) :
    boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inl j,p)=stepArchWeight N s i j p := by
  have hc : ValidBoundaryPath (stepBoundaryPorts N hN s) (N+1) i (.inl j,p) ↔
      i≠j ∧ PathBetween (N+1) (up i 0) (up j 0) p ∧ (∀v∈p,steppedDomain N s v) := by
    simp only [ValidBoundaryPath,stepBoundaryPorts,stepPort,retract_bottom,steppedVertices_embed]
    have hb : bottom i≠bottom j ↔ i≠j := by simp [bottom]
    rw [hb]
  unfold boundaryPathWeight stepArchWeight betweenArchWeight
  rw [hc]
  split_ifs <;> tauto

lemma boundaryPathWeight_step_side (N : ℕ) (hN : 1≤N) (s i : ℤ) (p : List Triangle) :
    boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inr ()),p)=stepSideWeight N s i p := by
  have hc : ValidBoundaryPath (stepBoundaryPorts N hN s) (N+1) i (.inr (.inr ()),p) ↔
      PathBetween (N+1) (up i 0) (up s N) p ∧ (∀v∈p,steppedDomain N s v) := by
    simp only [ValidBoundaryPath,stepBoundaryPorts,stepPort,retract_side,steppedVertices_embed]
    have hn : bottom i≠sidePort N s := by simp [bottom,sidePort]
    change (bottom i≠sidePort N s ∧ PathBetween (N+1) (up i 0) (up s N) p ∧ _) ↔ _
    exact and_iff_right hn
  simp only [boundaryPathWeight,stepSideWeight,hc]


 

 


lemma summable_sumProd {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E}
    (ha : Summable (fun x : A×C=>f (.inl x.1,x.2)))
    (hb : Summable (fun x : B×C=>f (.inr x.1,x.2))) : Summable f := by
  apply ((Equiv.sumProdDistrib A B C).symm.summable_iff).mp
  exact Summable.sum _ ha hb

lemma tsum_sumProd {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E}
    (ha : Summable (fun x : A×C=>f (.inl x.1,x.2)))
    (hb : Summable (fun x : B×C=>f (.inr x.1,x.2))) :
    (∑'x,f x)=(∑'x : A×C,f (.inl x.1,x.2))+(∑'x : B×C,f (.inr x.1,x.2)) := by
  rw [←(Equiv.sumProdDistrib A B C).symm.tsum_eq f]
  exact ha.tsum_sum hb

lemma phase_re (k : ℤ) : (Diagram.phase^k).re=Real.cos ((k:ℝ)*lambda) := by
  rw [Diagram.phase_pow]
  simp [Complex.exp_re,Diagram.lambda,lambda]

lemma phase_im (k : ℤ) : (Diagram.phase^k).im=Real.sin ((k:ℝ)*lambda) := by
  rw [Diagram.phase_pow]
  simp [Complex.exp_im,Diagram.lambda,lambda]

variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

lemma boundary_complex_summable (hs : Summable (boundaryPathWeight P H i)) (θ : B→ℤ) :
    Summable (fun x : B×List Triangle=>(boundaryPathWeight P H i x:ℂ)*Diagram.phase^(θ x.1)) := by
  apply hs.of_norm_bounded
  intro x
  simp [norm_zpow,phase_norm,Real.norm_of_nonneg (boundaryPathWeight_nonneg P H i x)]

lemma boundary_real_summable (hs : Summable (boundaryPathWeight P H i)) (θ : B→ℤ) :
    Summable (fun x : B×List Triangle=>boundaryPathWeight P H i x*Real.cos ((θ x.1:ℝ)*lambda)) := by
  have hh := (Complex.hasSum_re (boundary_complex_summable P hs θ).hasSum).summable
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,phase_re] using hh

lemma boundary_imaginary_summable (hs : Summable (boundaryPathWeight P H i)) (θ : B→ℤ) :
    Summable (fun x : B×List Triangle=>boundaryPathWeight P H i x*Real.sin ((θ x.1:ℝ)*lambda)) := by
  have hh := (Complex.hasSum_im (boundary_complex_summable P hs θ).hasSum).summable
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,phase_im] using hh

 
theorem boundary_real_flux (hH : 1≤H) (hi : D (bottom i).1)
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (hs : Summable (boundaryPathWeight P H i))
    (θ : B→ℤ) (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'x : B×List Triangle,boundaryPathWeight P H i x*Real.cos ((θ x.1:ℝ)*lambda))=1 := by
  have hh:=congrArg Complex.re (boundary_flux P hH hi hD hs θ hθ)
  rw [Complex.re_tsum (boundary_complex_summable P hs θ)] at hh
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,phase_re,Complex.one_re] using hh

theorem boundary_imaginary_flux (hH : 1≤H) (hi : D (bottom i).1)
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (hs : Summable (boundaryPathWeight P H i))
    (θ : B→ℤ) (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'x : B×List Triangle,boundaryPathWeight P H i x*Real.sin ((θ x.1:ℝ)*lambda))=0 := by
  have hh:=congrArg Complex.im (boundary_flux P hH hi hD hs θ hθ)
  rw [Complex.im_tsum (boundary_complex_summable P hs θ)] at hh
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,phase_im,Complex.one_im] using hh

lemma stripBoundary_summable (H : ℕ) (hH : 1≤H) (i : ℤ) :
    Summable (boundaryPathWeight (stripBoundaryPorts H hH) H i) := by
  apply summable_sumProd
  · simpa only [boundaryPathWeight_strip_bottom] using betweenArchWeight_summable H hH i
  · simpa only [boundaryPathWeight_strip_top] using betweenBridgeWeight_summable H hH i

def stripTurn (i : ℤ) : ℤ⊕ℤ→ℤ
  | .inl j=>if i≤j then -3 else 3
  | .inr _=>0

lemma strip_turn (H : ℕ) (hH : 1≤H) (i : ℤ) (x : ExitWord (bandVertices H) i) :
    turn x.val=stripTurn i (exitPort (stripBoundaryPorts H hH) x) := by
  have ht:=exitPort_terminal (stripBoundaryPorts H hH) x
  generalize hb : exitPort (stripBoundaryPorts H hH) x=b at ht ⊢
  rcases b with j|j
  · exact bottom_turn i j x.val x.property.1 (ribbonSimple_of_nodup x.property.2.1)
      (fun v hv=>(x.property.2.2.1 v hv).1) ht
  · exact top_turn H hH i j x.val x.property.1 x.property.2.1 x.property.2.2.1 ht

lemma stripTurn_cos_bottom (i j : ℤ) : Real.cos ((stripTurn i (.inl j):ℝ)*lambda)=c := by
  dsimp only [stripTurn]
  split_ifs <;> norm_num [neg_mul,Real.cos_neg,c,lambda] <;> congr 1 <;> ring

lemma stripTurn_cos_top (i j : ℤ) : Real.cos ((stripTurn i (.inr j):ℝ)*lambda)=1 := by
  simp [stripTurn]

 

theorem physical_strip_flux {H : ℕ} (hH : 1≤H) : c*archMass H+bridgeMass H=1 := by
  have ha:=betweenArchWeight_summable H hH 0
  have hb:=betweenBridgeWeight_summable H hH 0
  have hf:=boundary_real_flux (stripBoundaryPorts H hH) hH (by dsimp [bandVertices,bottom]; omega)
    (fun v hv=>hv) (stripBoundary_summable H hH 0) (stripTurn 0) (strip_turn H hH 0)
  have ht := tsum_sumProd (f:=fun x : (ℤ⊕ℤ)×List Triangle=>
      boundaryPathWeight (stripBoundaryPorts H hH) H 0 x*Real.cos ((stripTurn 0 x.1:ℝ)*lambda))
    (by simpa only [boundaryPathWeight_strip_bottom,stripTurn_cos_bottom] using ha.mul_right c)
    (by simpa only [boundaryPathWeight_strip_top,stripTurn_cos_top,mul_one] using hb)
  simp only [boundaryPathWeight_strip_bottom,boundaryPathWeight_strip_top,
    stripTurn_cos_bottom,stripTurn_cos_top,mul_one] at ht
  rw [ht,tsum_mul_right,ha.tsum_prod,hb.tsum_prod] at hf
  have hac (j : ℤ) : (∑'p,betweenArchWeight H 0 j p)=K H j := by
    change betweenArchKernel H 0 j=K H j
    simp only [betweenArchKernel_eq,sub_zero]
  have hbc (j : ℤ) : (∑'p,betweenBridgeWeight H 0 j p)=bridgeKernel H j := by
    apply tsum_congr
    intro p
    simp only [betweenBridgeWeight,bridgeWeight,pathBetween_source]
  simpa only [hac,hbc,archMass,bridgeMass,mul_comm] using hf

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

 

def extendStepTop (N : ℕ) (s j : ℤ) (p : List Triangle) : List Triangle :=
  if j<s then p++[up j N,down j N] else p

lemma extendStepTop_injective (N : ℕ) (s j : ℤ) : Function.Injective (extendStepTop N s j) := by
  intro p q h
  unfold extendStepTop at h
  split_ifs at h
  · exact List.append_cancel_right h
  · exact h

lemma extendStepTop_spec {N : ℕ} (hN : 1≤N) (s i j : ℤ) {p : List Triangle}
    (hp : ValidBoundaryPath (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl j),p)) :
    PathBetween (N+1) (up i 0) (down j N) (extendStepTop N s j p) := by
  have hpath:=hp.2.1
  change PathBetween (N+1) (up i 0) (retractVertex (stepTop N s j).1) p at hpath
  have hD : ∀v∈p,steppedDomain N s v := fun v hv=>
    (steppedVertices_embed N s v).mp (hp.2.2 v hv)
  by_cases hj : j<s
  · rw [stepTop,ite_eq_left hj,retract_top N hN] at hpath
    have hu : up j N∉p := by
      intro hm
      have he:=hD _ hm
      dsimp [steppedDomain,up] at he
      omega
    have hd : down j N∉p := by
      intro hm
      have he:=hD _ hm
      dsimp [steppedDomain,down] at he
      omega
    have hdu : adjacent (down j (N-1)) (up j N) := by
      simp [adjacent,upDownAdjacent,up,down]
      omega
    have hud : adjacent (up j N) (down j N) := by simp [adjacent,upDownAdjacent,up,down]
    have hp':=(hpath.append_vertex (Nat.lt_succ_self N) hu hdu).append_vertex
      (Nat.lt_succ_self N) (by simpa only [List.mem_append,List.mem_singleton,down,up,Prod.mk.injEq,Bool.false_eq_true,and_false,or_false] using hd) hud
    simpa [extendStepTop,hj,List.append_assoc] using hp'
  · rw [stepTop,ite_eq_right hj,retract_top (N+1) (by omega)] at hpath
    simpa [extendStepTop,hj] using hpath

lemma extendStepTop_weight {N : ℕ} (hN : 1≤N) (s i j : ℤ) (p : List Triangle) :
    rho^2*boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl j),p) ≤
      betweenBridgeWeight (N+1) i j (extendStepTop N s j p) := by
  unfold boundaryPathWeight
  split_ifs with hp
  · have hB : 0<N+1 ∧ PathBetween (N+1) (up i 0) (down j ((N+1)-1)) (extendStepTop N s j p) :=
      ⟨by omega,by simpa using extendStepTop_spec hN s i j hp⟩
    rw [betweenBridgeWeight,ite_eq_left hB]
    by_cases hj : j<s
    · simp only [extendStepTop,ite_eq_left hj,List.length_append,List.length_cons,List.length_nil]
      rw [pow_add]
      simp [mul_comm]
    · simp only [extendStepTop,ite_eq_right hj]
      have hr : rho^2≤1 := rho_sq_lt_one.le
      exact (mul_le_mul_of_nonneg_right hr (pow_nonneg rho_pos.le _)).trans_eq (one_mul _)
  · simp only [mul_zero]
    exact betweenBridgeWeight_nonneg _ _ _ _

lemma stepBoundary_top_summable {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>
      boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl x.1),x.2)) := by
  let e : ℤ×List Triangle→ℤ×List Triangle := fun x=>(x.1,extendStepTop N s x.1 x.2)
  have he : Function.Injective e := by
    intro x y hh
    have hj:=congrArg Prod.fst hh
    change x.1=y.1 at hj
    have hp:=congrArg Prod.snd hh
    change extendStepTop N s x.1 x.2=extendStepTop N s y.1 y.2 at hp
    rw [hj] at hp
    exact Prod.ext hj (extendStepTop_injective N s y.1 hp)
  have hg:=(betweenBridgeWeight_summable (N+1) (by omega) i).comp_injective he
  have hm : Summable (fun x : ℤ×List Triangle=>rho^2*
      boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl x.1),x.2)) :=
    hg.of_nonneg_of_le (fun x=>mul_nonneg (sq_nonneg _) (boundaryPathWeight_nonneg _ _ _ _))
      (fun x=>extendStepTop_weight hN s i x.1 x.2)
  exact (summable_mul_left_iff (pow_ne_zero _ rho_pos.ne')).mp hm

lemma stepArchWeight_summable {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>stepArchWeight N s i x.1 x.2) :=
  (betweenArchWeight_summable (N+1) (by omega) i).of_nonneg_of_le
    (fun x=>stepArchWeight_nonneg N s i x.1 x.2) (fun x=>stepArchWeight_le N s i x.1 x.2)

 

theorem stepBoundary_summable {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    Summable (boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i) := by
  apply summable_sumProd
  · simpa only [boundaryPathWeight_step_bottom] using stepArchWeight_summable hN s i
  · apply summable_sumProd
    · exact stepBoundary_top_summable hN s i
    · have hs := (stepSideWeight_summable s (stripSumsFinite (show 1≤N+1 by omega))).prod_factor i
      apply (summable_prod_of_nonneg (fun x=>boundaryPathWeight_nonneg _ _ _ _)).mpr
      refine ⟨?_,(hasSum_fintype _).summable⟩
      intro u
      cases u
      simpa only [boundaryPathWeight_step_side] using hs


 

 


lemma summable_sumProd_left {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E} (hf : Summable f) :
    Summable (fun x : A×C=>f (.inl x.1,x.2)) := by
  apply hf.comp_injective
  intro x y h
  exact Prod.ext (Sum.inl.inj (congrArg (fun z : (A⊕B)×C=>z.1) h)) (congrArg (fun z : (A⊕B)×C=>z.2) h)

lemma summable_sumProd_right {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E} (hf : Summable f) :
    Summable (fun x : B×C=>f (.inr x.1,x.2)) := by
  apply hf.comp_injective
  intro x y h
  exact Prod.ext (Sum.inr.inj (congrArg (fun z : (A⊕B)×C=>z.1) h)) (congrArg (fun z : (A⊕B)×C=>z.2) h)

def stepTurn (i : ℤ) : StepEndpoint→ℤ
  | .inl j=>if i≤j then -3 else 3
  | .inr (.inl _)=>0
  | .inr (.inr _)=>1

lemma step_turn (N : ℕ) (hN : 1≤N) (s i : ℤ) (x : ExitWord (steppedVertices N s) i) :
    turn x.val=stepTurn i (exitPort (stepBoundaryPorts N hN s) x) := by
  have ht:=exitPort_terminal (stepBoundaryPorts N hN s) x
  generalize hb : exitPort (stepBoundaryPorts N hN s) x=b at ht ⊢
  rcases b with j|(j|u)
  · exact bottom_turn i j x.val x.property.1 (ribbonSimple_of_nodup x.property.2.1)
      (fun v hv=>(x.property.2.2.1 v hv).1) ht
  · exact step_top_turn N hN s i j x.val x.property.1 x.property.2.1 x.property.2.2.1 ht
  · exact step_side_turn N s i x.val x.property.1 x.property.2.1 x.property.2.2.1 ht

lemma stepTurn_sine_right (i : ℤ) (n : ℕ) :
    Real.sin ((stepTurn i (.inl (i+(n:ℤ)+1)):ℝ)*lambda) = -Real.sin (3*lambda) := by
  have hh : i≤ i+(n:ℤ)+1 := by omega
  simp [stepTurn,hh,neg_mul,Real.sin_neg]

lemma stepTurn_sine_left (i : ℤ) (n : ℕ) :
    Real.sin ((stepTurn i (.inl (i-1-(n:ℤ))):ℝ)*lambda) = Real.sin (3*lambda) := by
  have hh : ¬(i≤ i-1-(n:ℤ)) := by omega
  simp [stepTurn,hh]

lemma stepArchKernel_self (N : ℕ) (s i : ℤ) : stepArchKernel N s i i=0 := by
  simp [stepArchKernel,stepArchWeight,betweenArchWeight]

lemma step_bottom_imaginary_tsum {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    (∑'x : ℤ×List Triangle,stepArchWeight N s i x.1 x.2 * Real.sin ((stepTurn i (.inl x.1):ℝ)*lambda))=
    Real.sin (3*lambda)*(stepArchLeft N s i-stepArchRight N s i) := by
  have hB:=summable_sumProd_left (boundary_imaginary_summable (stepBoundaryPorts N hN s)
    (stepBoundary_summable hN s i) (stepTurn i))
  simp only [boundaryPathWeight_step_bottom] at hB
  let f : ℤ→ℝ:=fun j=>stepArchKernel N s i j * Real.sin ((stepTurn i (.inl j):ℝ)*lambda)
  have hprod (j : ℤ) : (∑'p,stepArchWeight N s i j p * Real.sin ((stepTurn i (.inl j):ℝ)*lambda))=f j := by
    rw [tsum_mul_right]; rfl
  have hf : Summable f := hB.prod.congr hprod
  have hr := hf.comp_injective (i:=fun n : ℕ=>i+(n:ℤ)+1) (by intro a b hh; dsimp at hh; omega)
  have hl := hf.comp_injective (i:=fun n : ℕ=>i-1-(n:ℤ)) (by intro a b hh; dsimp at hh; omega)
  have he (n : ℕ) : i+ -((n:ℤ)+1)=i-1-(n:ℤ) := by ring
  have hh := tsum_of_add_one_of_neg_add_one (f:=fun j : ℤ=>f (i+j))
    (by simpa only [Function.comp_def,add_assoc] using hr)
    (by simpa only [Function.comp_def,he] using hl)
  rw [hB.tsum_prod]
  simp_rw [hprod]
  rw [←(Equiv.addLeft i).tsum_eq f]
  change (∑'j : ℤ,f (i+j))=_
  rw [hh]
  have hr' (n : ℕ) : f (i+((n:ℤ)+1)) = stepArchKernel N s i (i+(n:ℤ)+1) * (-Real.sin (3*lambda)) := by
    simp only [f,←add_assoc,stepTurn_sine_right]
  have hl' (n : ℕ) : f (i+ -((n:ℤ)+1)) = stepArchKernel N s i (i-1-(n:ℤ)) * Real.sin (3*lambda) := by
    simp only [f,he,stepTurn_sine_left]
  have hz : f (i+0)=0 := by simp only [f,add_zero,stepArchKernel_self,zero_mul]
  simp_rw [hr',hl',hz,add_zero,tsum_mul_right]
  change stepArchRight N s i * (-Real.sin (3*lambda)) + stepArchLeft N s i * Real.sin (3*lambda) = _
  ring

 

theorem physical_stepped_flux {N : ℕ} (hN : 1≤N) (s : ℤ) : SteppedBoundaryFlux N s := by
  intro i
  let P:=stepBoundaryPorts N hN s
  let F : StepEndpoint×List Triangle→ℝ :=
    fun x=>boundaryPathWeight P (N+1) i x*Real.sin ((stepTurn i x.1:ℝ)*lambda)
  have hs : Summable F := boundary_imaginary_summable P (stepBoundary_summable hN s i) (stepTurn i)
  have hf : (∑'x,F x)=0 := boundary_imaginary_flux P (by omega)
    (by dsimp [steppedVertices,bottom]; omega) (steppedVertices_bound N s)
      (stepBoundary_summable hN s i) (stepTurn i) (step_turn N hN s i)
  have hb:=summable_sumProd_left hs
  have hn:=summable_sumProd_right hs
  have ht:=summable_sumProd_left hn
  have hp:=summable_sumProd_right hn
  have hsplit : (∑'x : ℤ×List Triangle,F (.inl x.1,x.2)) +
      ((∑'x : ℤ×List Triangle,F (.inr (.inl x.1),x.2)) +
       (∑'x : Unit×List Triangle,F (.inr (.inr x.1),x.2)))=0 :=
    (congrArg (fun y : ℝ => (∑'x : ℤ×List Triangle,F (.inl x.1,x.2)) + y)
      (tsum_sumProd (f:=fun x : (ℤ⊕Unit)×List Triangle => F (.inr x.1,x.2)) ht hp)).symm.trans ((tsum_sumProd (f:=F) hb hn).symm.trans hf)
  have hbot : (∑'x : ℤ×List Triangle,F (.inl x.1,x.2))=
      Real.sin (3*lambda)*(stepArchLeft N s i-stepArchRight N s i) := by
    simpa only [F,P,boundaryPathWeight_step_bottom] using step_bottom_imaginary_tsum hN s i
  have htop : (∑'x : ℤ×List Triangle,F (.inr (.inl x.1),x.2))=0 := by
    simp [F,stepTurn]
  have hside : (∑'x : Unit×List Triangle,F (.inr (.inr x.1),x.2))=
      Real.sin lambda*stepSideKernel N s i := by
    rw [hp.tsum_prod]
    simp [F,P,stepTurn,boundaryPathWeight_step_side,tsum_mul_left,stepSideKernel,mul_comm]
  have hvalue := congrArg₂ (fun a b : ℝ => a+b) hbot
    (congrArg₂ (fun a b : ℝ => a+b) htop hside)
  have hresult := hvalue.symm.trans hsplit
  simpa only [zero_add] using hresult

end
end CriticalStrip.HoneycombBranch

 

 

namespace CriticalStrip

 

theorem critical_strip_mass : CriticalStripMass := by
  exact criticalStripMass_of_physical_identities
    (fun _ hN => stripSumsFinite hN)
    (fun _ hN => HoneycombBranch.physical_strip_flux hN)
    (fun _ hN => ⟨0,HoneycombBranch.physical_stepped_flux hN 0⟩)
    (fun _ hN => physical_arch_formula hN)

end CriticalStrip

end OAI

import OAI.Analysis.InterpolatedFactors.AmbientSystem

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45 u_46 u_47 u_48
universe u_49

open Filter Topology

namespace FreeFock
open Filter Topology
open scoped ENNReal
variable {α : Type u_6} [DecidableEq α]

 theorem semicircular_no_eigenprojection (i : α) (z : ℂ) (E : gaussianAlgebra α)
    (hE : IsStarProjection (E : Operator α))
    (hA : semicircular i*(E : Operator α)=z • (E : Operator α)) : E=0 := by
  have he : semicircular i ((E : Operator α) vacuum)=z • ((E : Operator α) vacuum) :=
    DFunLike.congr_fun hA vacuum
  have hr := semicircular_eigen_root_zero i z _ he
  have hvac : (E : Operator α) vacuum=0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      inner ℂ ((E : Operator α) vacuum) ((E : Operator α) vacuum)=
          inner ℂ vacuum (star (E : Operator α) ((E : Operator α) vacuum)) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ vacuum ((E : Operator α) vacuum) := by
        rw [hE.isSelfAdjoint.star_eq]
        have hh := DFunLike.congr_fun hE.isIdempotentElem.eq vacuum
        rw [mul_apply_eq_comp] at hh
        rw [hh]
      _ = 0 := by simp [vacuum,lp.inner_single_left,RCLike.inner_apply] at hr ⊢;exact hr
  exact gaussian_separating E hvac

end FreeFock
open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace CyclicSpectral
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
end CyclicSpectral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace CyclicSpectral

section
open MeasureTheory
variable {H : Type u_19} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_20} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_21} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end CyclicSpectral
namespace FreeFock

section
open MeasureTheory
variable {α : Type u_22} [DecidableEq α]
local instance : InnerProductSpace ℝ (Fock α) := InnerProductSpace.rclikeToReal ℂ (Fock α)

end
open MeasureTheory
variable {α : Type u_23} [DecidableEq α]

instance semicircular_spectral_probability (i : α) :
    IsProbabilityMeasure (CyclicSpectral.measure (semicircular i) (semicircular_selfAdjoint i) vacuum) := by
  apply CyclicSpectral.probability
  simp [vacuum,lp.norm_single]

instance semicircular_spectral_diffuse (i : α) :
    NullSingletonClass (CyclicSpectral.measure (semicircular i) (semicircular_selfAdjoint i) vacuum) :=
  semicircular_spectral_noAtoms i

 theorem spectralHaar_mem (i : α) :
    (CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum : Operator α)
      ∈ gaussianAlgebra α := by
  apply CyclicSpectral.complexHom_mem
  · rw [gaussianAlgebra,StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  · exact StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
      (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))

def spectralHaar (i : α) : unitary (gaussianAlgebra α) := by
  let U := CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum
  refine ⟨⟨U,spectralHaar_mem i⟩,Unitary.mem_iff.mpr ⟨?_,?_⟩⟩
  · apply Subtype.ext
    exact (Unitary.mem_iff.mp U.property).1
  · apply Subtype.ext
    exact (Unitary.mem_iff.mp U.property).2

 theorem spectralHaar_moment (i : α) (n : ℕ) :
    vacuumTrace ((((spectralHaar i : gaussianAlgebra α) : Operator α)^n))=if n=0 then 1 else 0 :=
  CyclicSpectral.haarUnitary_moment (semicircular i) (semicircular_selfAdjoint i) vacuum n

end FreeFock
open Filter Topology
open scoped ENNReal
 theorem lp_strong_limit_of_bounded_basis {α : Type u_24} [DecidableEq α]
    (T : ℕ → lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2)
    (A : lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2)
    (C : ℝ) (hbound : ∀ n, ‖T n‖ ≤ C)
    (hbasis : ∀ a, Tendsto (fun n => T n (lp.single 2 a 1)) atTop (𝓝 (A (lp.single 2 a 1))))
    (ξ : lp (fun _ : α => ℂ) 2) : Tendsto (fun n => T n ξ) atTop (𝓝 (A ξ)) := by
  have heq : Equicontinuous (fun n => (T n : lp (fun _ : α => ℂ) 2 → lp (fun _ : α => ℂ) 2)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C*r)
      (by simpa using (tendsto_const_nhds.mul (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))))
    intro x y n
    rw [dist_eq_norm,← map_sub]
    exact (T n).le_opNorm (x-y) |>.trans
      (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg (x-y)))
  have hc := heq.isClosed_setOfPred_tendsto (l := atTop) A.continuous
  apply hc.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  have hs (a : α) : Tendsto (fun n => T n (lp.single 2 a (ξ a))) atTop (𝓝 (A (lp.single 2 a (ξ a)))) := by
    have h : lp.single (E := fun _ : α => ℂ) 2 a (ξ a)=(ξ a) • lp.single 2 a 1 := by
      ext b
      simp [lp.single_apply,Pi.single_apply]
    simpa only [h,map_smul] using (hbasis a).const_smul (ξ a)
  simpa only [map_sum] using tendsto_finsetSum s (fun a _ => hs a)
namespace FreeFock

section
open Filter Topology Set MeasureTheory
variable {α : Type u_25} [DecidableEq α]

 theorem semicircular_mem_haar_bicommutant (i : α) :
    semicircular i ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ ({(CyclicSpectral.haarUnitary (semicircular i)
        (semicircular_selfAdjoint i) vacuum : Operator α)} : Set (Operator α)) : Set (Operator α)) := by
  let : Nontrivial (Fock α) := ⟨⟨vacuum,0,by
    intro h
    have he := congrArg (fun v : Fock α => v []) h
    simp [vacuum,lp.single_apply] at he⟩⟩
  have hb (n : ℕ) := CyclicSpectral.bounded_haar_approx (semicircular i)
    (semicircular_selfAdjoint i) vacuum (1/((n:ℝ)+1)) (by positivity)
  choose T hmem hnorm herr using hb
  have hS : semicircular i ∈ gaussianAlgebra α :=
    StarAlgebra.adjoin_le_centralizer_centralizer ℂ _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))
  have hG : IsClosed (gaussianAlgebra α : Set (Operator α)) := by
    rw [gaussianAlgebra,StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have hT (n : ℕ) : T n ∈ gaussianAlgebra α :=
    StarAlgebra.elemental.le_of_mem hG (spectralHaar_mem i) (hmem n)
  have hv : Tendsto (fun n => T n vacuum) atTop (𝓝 (semicircular i vacuum)) := by
    have h := squeeze_zero_norm (fun n => (herr n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh := h.add_const (semicircular i vacuum)
    simpa only [sub_add_cancel,zero_add] using hh
  have hstrong : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (semicircular i ξ)) := by
    apply lp_strong_limit_of_bounded_basis T (semicircular i) ‖semicircular i‖ hnorm
    intro w
    have he (D : Operator α) (hD : D ∈ gaussianAlgebra α) :
        D (lp.single 2 w 1)=rightWick w.reverse (D vacuum) := by
      have h := DFunLike.congr_fun (gaussian_commute_rightWick ⟨D,hD⟩ w.reverse) vacuum
      simpa only [mul_apply_eq_comp,rightWick_vacuum,List.reverse_reverse] using h.symm
    simpa only [he _ (hT _),he _ hS,Function.comp_def] using (rightWick w.reverse).continuous.continuousAt.tendsto.comp hv
  let B := StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ ({(CyclicSpectral.haarUnitary (semicircular i)
        (semicircular_selfAdjoint i) vacuum : Operator α)} : Set (Operator α)) : Set (Operator α))
  have hB : IsClosed (B : Set (Operator α)) := by
    dsimp [B]
    exact Set.isClosed_centralizer _
  have hU : (CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum : Operator α) ∈ B :=
    StarAlgebra.adjoin_le_centralizer_centralizer ℂ _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _))
  have hTB (n : ℕ) : T n ∈ B := StarAlgebra.elemental.le_of_mem hB hU (hmem n)
  rw [StarSubalgebra.mem_centralizer_iff]
  intro C hC
  have hl (D : Operator α) (hD : D ∈ StarSubalgebra.centralizer ℂ
      ({(CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum : Operator α)} : Set (Operator α))) :
      D*semicircular i=semicircular i*D := by
    apply ContinuousLinearMap.ext
    intro ξ
    have he n := congrArg (fun Q : Operator α => Q ξ)
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hTB n) D hD).1
    exact tendsto_nhds_unique ((D.continuous.continuousAt.tendsto.comp (hstrong ξ)).congr
      (fun n => he n)) (hstrong (D ξ))
  exact ⟨hl C hC,hl (star C) (star_mem hC)⟩
end
section
open Set
variable {α : Type u_26} [DecidableEq α]

def spectralHaarOperator (i : α) : Operator α :=
  CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum

theorem haar_gaussian_commutant :
    StarSubalgebra.centralizer ℂ (Set.range (spectralHaarOperator : α → Operator α))=gaussianCommutant α := by
  ext C
  constructor
  · intro hC
    rw [gaussianCommutant,StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨i,rfl⟩
    have hi : C ∈ StarSubalgebra.centralizer ℂ ({spectralHaarOperator i} : Set (Operator α)) :=
      StarSubalgebra.centralizer_le ℂ _ _ (Set.singleton_subset_iff.mpr (Set.mem_range_self i)) hC
    have hh := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (semicircular_mem_haar_bicommutant i) C hi).1
    exact ⟨hh.symm,by rw [(semicircular_selfAdjoint i).star_eq]; exact hh.symm⟩
  · intro hC
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨i,rfl⟩
    have hi : spectralHaarOperator i ∈ gaussianAlgebra α := spectralHaar_mem i
    exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hi C hC).1.symm,
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (show star (spectralHaarOperator i) ∈ gaussianAlgebra α from star_mem hi) C hC).1.symm⟩

theorem haar_generated_gaussian :
    StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Set.range (spectralHaarOperator : α → Operator α)) : Set (Operator α))=
    gaussianAlgebra α := by
  rw [haar_gaussian_commutant]
  rfl
end

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_28} [DecidableEq α]

 theorem spectralHaar_cyclic_total :
    (algebraCyclic (StarAlgebra.adjoin ℂ (Set.range (spectralHaarOperator : α → Operator α)))
      vacuum).topologicalClosure=⊤ := by
  let A := StarAlgebra.adjoin ℂ (Set.range (spectralHaarOperator : α → Operator α))
  let K := (algebraCyclic A vacuum).topologicalClosure
  have hδ (w : List α) : lp.single 2 w (1:ℂ) ∈ K := by
    have hw : wick w ∈ gaussianAlgebra α := wick_mem_any _
      (fun i => StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
        (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))) w
    rw [← haar_generated_gaussian] at hw
    have hh := bicommutant_vector_mem_cyclic (Set.range (spectralHaarOperator : α → Operator α))
      vacuum (wick w) hw
    simpa only [wick_vacuum] using hh
  apply top_unique
  intro ξ _
  apply (algebraCyclic A vacuum).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : List α => ℂ) 2 w (ξ w)=(ξ w) • lp.single 2 w 1 := by
    ext v
    simp [lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hδ w)

end
section
open scoped ComplexConjugate
variable {α : Type u_29} [DecidableEq α]

 theorem vacuumTrace_star (T : Operator α) : vacuumTrace (star T)=conj (vacuumTrace T) := by
  unfold vacuumTrace
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (T vacuum) vacuum).symm

 theorem spectralHaar_integer_moment (i : α) (k : ℤ) :
    vacuumTrace (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)=
      if k=0 then 1 else 0 := by
  cases k with
  | ofNat n =>
    simpa using spectralHaar_moment i n
  | negSucc n =>
    rw [ite_eq_right (Int.negSucc_ne_zero n),zpow_negSucc,← Unitary.star_eq_inv]
    change vacuumTrace (star ((((spectralHaar i : gaussianAlgebra α) : Operator α)^(n+1))))=0
    rw [vacuumTrace_star,spectralHaar_moment]
    simp

end
section
variable {α : Type u_30} [DecidableEq α]

 theorem wick_replicate_boundary (i j : α) (hij : i≠j) (w : List α) (n : ℕ) :
    wick (List.replicate n i)*wick (j::w)=wick (List.replicate n i++j::w) := by
  suffices ∀ n, (wick (List.replicate n i)*wick (j::w)=wick (List.replicate n i++j::w)) ∧
      (wick (List.replicate (n+1) i)*wick (j::w)=wick (List.replicate (n+1) i++j::w)) from (this n).1
  intro n
  induction n with
  | zero =>
    constructor
    · simp
    · simp only [Nat.zero_add,List.replicate_one,List.cons_append,List.nil_append]
      rw [wick_semicircular_cons i [],wick_nil,mul_one,sub_zero,
        wick_semicircular_cons i (j::w)]
      simp only [hij,ite_false,sub_zero]
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    have hleft : wick (List.replicate (n+1+1) i)=
        semicircular i*wick (List.replicate (n+1) i)-wick (List.replicate n i) := by
      conv_lhs => rw [List.replicate_succ,wick_semicircular_cons]
      simp only [List.replicate_succ,ite_true]
    have hright : wick (List.replicate (n+1+1) i++j::w)=
        semicircular i*wick (List.replicate (n+1) i++j::w)-wick (List.replicate n i++j::w) := by
      conv_lhs => rw [List.replicate_succ,List.cons_append,wick_semicircular_cons]
      simp only [List.replicate_succ,List.cons_append,ite_true]
    rw [hleft,sub_mul,mul_assoc,ih.1,ih.2,hright]
end
variable {α : Type u_31} [DecidableEq α]

def blockLetters (L : List (α × ℕ)) : List α :=
  L.flatMap (fun p => List.replicate p.2 p.1)

def blockProduct : List (α × ℕ) → Operator α
  | [] => 1
  | (i,n)::L => wick (List.replicate n i)*blockProduct L

def blocksReduced : List (α × ℕ) → Prop
  | [] => True
  | (i,n)::L => 0 < n ∧ blocksReduced L ∧
    match L with | [] => True | (j,_)::_ => i≠j

 theorem wick_blocks_concatenate (L : List (α × ℕ)) (hL : blocksReduced L) :
    blockProduct L=wick (blockLetters L) := by
  induction L with
  | nil => simp [blockProduct,blockLetters]
  | cons p L ih =>
    rcases p with ⟨i,n⟩
    obtain ⟨hn,hL,hsep⟩ := hL
    cases L with
    | nil => simp [blockProduct,blockLetters]
    | cons q L =>
      rcases q with ⟨j,m⟩
      have hm : 0 < m := hL.1
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      rw [blockProduct,ih hL]
      change wick (List.replicate n i)*wick ((List.replicate (k+1) j)++blockLetters L)=
        wick (List.replicate n i++(List.replicate (k+1) j++blockLetters L))
      simpa only [List.replicate_succ,List.cons_append] using
        wick_replicate_boundary i j hsep (List.replicate k j++blockLetters L) n

 omit [DecidableEq α] in
 theorem blockLetters_nonempty {L : List (α × ℕ)} (hL : blocksReduced L) (h : L≠[]) :
    blockLetters L≠[] := by
  cases L with
  | nil => exact False.elim (h rfl)
  | cons p L =>
    rcases p with ⟨i,n⟩
    have hn : 0 < n := hL.1
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp [blockLetters,List.replicate_succ]

 theorem wick_blocks_centered_moment (L : List (α × ℕ)) (hL : blocksReduced L) (h : L≠[]) :
    vacuumTrace (blockProduct L)=0 := by
  rw [wick_blocks_concatenate L hL]
  have hne := blockLetters_nonempty hL h
  unfold vacuumTrace
  rw [wick_vacuum]
  simp [vacuum,lp.inner_single_left,lp.single_apply,hne]
end FreeFock
section

variable {A : Type u_32} [NormedRing A] [NormedAlgebra ℂ A]

theorem mul_mem_closed_span_image2 (s t : Set A) (x y : A)
    (hx : x∈(Submodule.span ℂ s).topologicalClosure)
    (hy : y∈(Submodule.span ℂ t).topologicalClosure) :
    x*y∈(Submodule.span ℂ (Set.image2 (·*·) s t)).topologicalClosure := by
  let K := (Submodule.span ℂ (Set.image2 (·*·) s t)).topologicalClosure
  have hbase (b : A) (hb : b∈t) : x*b∈K := by
    have hc : IsClosed {a : A | a*b∈K} :=
      (Submodule.isClosed_topologicalClosure _).preimage (continuous_id.mul continuous_const)
    apply closure_minimal (t := {a : A | a*b∈K}) ?_ hc hx
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨a,ha,b,hb,rfl⟩)
    | zero => simp
    | add a c _ _ ha hc => simpa only [Set.mem_ofPred_eq,add_mul] using K.add_mem ha hc
    | smul z a _ ha => simpa only [Set.mem_ofPred_eq,smul_mul_assoc] using K.smul_mem z ha
  have hc : IsClosed {b : A | x*b∈K} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)
  apply closure_minimal (t := {b : A | x*b∈K}) ?_ hc hy
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb => exact hbase b hb
  | zero => simp
  | add b c _ _ hb hc => simpa only [Set.mem_ofPred_eq,mul_add] using K.add_mem hb hc
  | smul z b _ hb => simpa only [Set.mem_ofPred_eq,mul_smul_comm] using K.smul_mem z hb

end
namespace FreeFock

section
variable {α : Type u_33} [DecidableEq α]

 theorem center_run_mem (i : α) (x : Operator α) (hx : x∈runSpan i) :
    x-vacuumTrace x • 1∈positiveRunSpan i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    cases n with
    | zero => simp [vacuumTrace_one]
    | succ n =>
      rw [vacuumTrace_run,ite_eq_right (Nat.succ_ne_zero n),zero_smul ℂ (A := Operator α),sub_zero]
      exact Submodule.subset_span (Set.mem_range_self n)
  | zero => simpa only [vacuumTrace_linear.map_zero,zero_smul ℂ (A := Operator α),sub_self] using (positiveRunSpan i).zero_mem
  | add x y _ _ hx hy =>
    rw [vacuumTrace_linear.map_add,add_smul (R := ℂ) (M := Operator α),add_sub_add_comm]
    exact (positiveRunSpan i).add_mem hx hy
  | smul c x _ hx =>
    rw [vacuumTrace_linear.map_smul,smul_eq_mul,← smul_smul,← smul_sub]
    exact (positiveRunSpan i).smul_mem c hx

 theorem center_run_closure (i : α) (x : Operator α)
    (hx : x∈(runSpan i).topologicalClosure) :
    x-vacuumTrace x • 1∈(positiveRunSpan i).topologicalClosure := by
  have hc : Continuous (fun x : Operator α => x-vacuumTrace x • 1) :=
    continuous_id.sub (vacuumTrace_continuous.smul continuous_const)
  apply closure_minimal (t := {x | x-vacuumTrace x • 1∈(positiveRunSpan i).topologicalClosure}) ?_ ?_ hx
  · intro a ha
    exact (positiveRunSpan i).le_topologicalClosure (center_run_mem i a ha)
  · exact (positiveRunSpan i).isClosed_topologicalClosure.preimage hc

 theorem spectralHaar_run_closure (i : α) :
    spectralHaarOperator i ∈ (runSpan i).topologicalClosure := by
  change spectralHaarOperator i ∈ (runAlgebra i).topologicalClosure
  apply CyclicSpectral.complexHom_mem
  · exact StarSubalgebra.isClosed_topologicalClosure _
  · apply StarSubalgebra.le_topologicalClosure
    change semicircular i∈runSpan i
    simpa [wick_semicircular_cons] using run_mem i 1

 theorem spectralHaar_power_positive_run_closure (i : α) (k : ℤ) (hk : k≠0) :
    ((((spectralHaar i)^k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) ∈
      (positiveRunSpan i).topologicalClosure := by
  have hrun : ((((spectralHaar i)^k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) ∈
      (runSpan i).topologicalClosure := by
    change ((↑((spectralHaar i)^k) : gaussianAlgebra α) : Operator α) ∈
      (runAlgebra i).topologicalClosure
    have hh : spectralHaarOperator i∈(runAlgebra i).topologicalClosure := spectralHaar_run_closure i
    cases k with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast,zpow_natCast]
      change spectralHaarOperator i^n ∈ (runAlgebra i).topologicalClosure
      exact pow_mem hh n
    | negSucc n =>
      rw [zpow_negSucc,← Unitary.star_eq_inv]
      change star (spectralHaarOperator i^(n+1))∈(runAlgebra i).topologicalClosure
      exact star_mem (pow_mem hh (n+1))
  have hc := center_run_closure i _ hrun
  rw [spectralHaar_integer_moment,ite_eq_right hk,zero_smul ℂ (A := Operator α),sub_zero] at hc
  exact hc

end
variable {α : Type u_34} [DecidableEq α]

def colorsReduced : List α → Prop
  | [] => True
  | i::L => colorsReduced L ∧ (match L with | [] => True | j::_ => i≠j)

def runProducts : List α → Set (Operator α)
  | [] => {1}
  | i::L => Set.image2 (·*·) (Set.range (fun n : ℕ => wick (List.replicate (n+1) i))) (runProducts L)

 theorem runProducts_blocks (L : List α) (X : Operator α) (hX : X∈runProducts L) :
    ∃ K : List (α×ℕ), K.map Prod.fst=L ∧ (∀ p∈K,0<p.2) ∧ X=blockProduct K := by
  induction L generalizing X with
  | nil => exact ⟨[],rfl,by simp,by simpa [runProducts,blockProduct] using hX⟩
  | cons i L ih =>
    obtain ⟨a,⟨n,rfl⟩,b,hb,rfl⟩ := hX
    obtain ⟨K,hK,hpos,rfl⟩ := ih b hb
    refine ⟨(i,n+1)::K,by simp [hK],?_,rfl⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.succ_pos n
    · exact hpos p hp

 omit [DecidableEq α] in
 theorem blocksReduced_of_colors (K : List (α×ℕ))
    (h : colorsReduced (K.map Prod.fst)) (hpos : ∀ p∈K,0<p.2) : blocksReduced K := by
  induction K with
  | nil => trivial
  | cons p K ih =>
    rcases p with ⟨i,n⟩
    refine ⟨hpos (i,n) (by simp),ih h.1 (fun p hp => hpos p (by simp [hp])),?_⟩
    cases K with
    | nil => trivial
    | cons q K => exact h.2

 theorem runProducts_trace_zero (L : List α) (h : colorsReduced L) (hne : L≠[])
    (X : Operator α) (hX : X∈runProducts L) : vacuumTrace X=0 := by
  obtain ⟨K,hK,hpos,rfl⟩ := runProducts_blocks L X hX
  apply wick_blocks_centered_moment
  · apply blocksReduced_of_colors K
    · simpa only [hK] using h
    · exact hpos
  · intro he
    apply hne
    simpa only [he,List.map_nil] using hK.symm

 theorem vacuumTrace_span_zero (S : Set (Operator α)) (hS : ∀ X∈S,vacuumTrace X=0)
    (X : Operator α) (hX : X∈(Submodule.span ℂ S).topologicalClosure) : vacuumTrace X=0 := by
  apply closure_minimal (t := {X : Operator α | vacuumTrace X=0}) ?_
    (isClosed_eq vacuumTrace_continuous continuous_const) hX
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX => exact hS X hX
  | zero => exact vacuumTrace_linear.map_zero
  | add X Y _ _ hX hY =>
    change vacuumTrace X=0 at hX
    change vacuumTrace Y=0 at hY
    simp only [Set.mem_ofPred_eq,vacuumTrace_linear.map_add,hX,hY,add_zero]
  | smul c X _ hX =>
    change vacuumTrace X=0 at hX
    simp only [Set.mem_ofPred_eq,vacuumTrace_linear.map_smul,hX,smul_zero]

def haarProduct : List (α×ℤ) → Operator α
  | [] => 1
  | (i,k)::L => (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)*haarProduct L

 theorem haarProduct_mem_runProducts (L : List (α×ℤ)) (hL : ∀ p∈L,p.2≠0) :
    haarProduct L∈(Submodule.span ℂ (runProducts (L.map Prod.fst))).topologicalClosure := by
  induction L with
  | nil =>
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (by simp [runProducts,haarProduct]))
  | cons p L ih =>
    rcases p with ⟨i,k⟩
    exact mul_mem_closed_span_image2 _ _ _ _
      (spectralHaar_power_positive_run_closure i k (hL (i,k) (by simp)))
      (ih (fun p hp => hL p (by simp [hp])))

 theorem spectralHaar_mixed_moment (L : List (α×ℤ))
    (hL : ∀ p∈L,p.2≠0) (hred : colorsReduced (L.map Prod.fst)) (hne : L≠[]) :
    vacuumTrace (haarProduct L)=0 := by
  apply vacuumTrace_span_zero (runProducts (L.map Prod.fst))
  · exact runProducts_trace_zero _ hred (by simpa using hne)
  · exact haarProduct_mem_runProducts L hL

end FreeFock

section
variable {α : Type u_35}

def adjacentDistinct : List α → Prop
  | [] => True
  | i::L => adjacentDistinct L ∧ (match L with | [] => True | j::_ => i≠j)

def expandSignedRuns (R : List ((α×Bool)×ℕ)) : List (α×Bool) :=
  R.flatMap (fun p => List.replicate p.2 p.1)

theorem reduced_signed_runs (L : List (α×Bool)) (hL : FreeGroup.IsReduced L) :
    ∃ R : List ((α×Bool)×ℕ), L=expandSignedRuns R ∧
      (∀ p∈R,0<p.2) ∧ adjacentDistinct (R.map (fun p => p.1.1)) := by
  classical
  induction L with
  | nil => exact ⟨[],rfl,by simp,by trivial⟩
  | cons x L ih =>
    have ht : FreeGroup.IsReduced L := hL.tail
    obtain ⟨R,hR,hpos,hred⟩ := ih ht
    rcases x with ⟨i,b⟩
    cases R with
    | nil =>
      have hnil : L=[] := hR
      subst L
      exact ⟨[((i,b),1)],by simp [expandSignedRuns],by simp,by trivial⟩
    | cons p R =>
      rcases p with ⟨⟨j,c⟩,m⟩
      have hm := hpos ((j,c),m) (by simp)
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      have he : L=(j,c)::(List.replicate n (j,c)++expandSignedRuns R) := by
        simpa [expandSignedRuns,List.replicate_succ] using hR
      by_cases hij : i=j
      · subst j
        have hpair : FreeGroup.IsReduced ((i,b)::(i,c)::(List.replicate n (i,c)++expandSignedRuns R)) := by
          simpa only [he] using hL
        have hbc : b=c := (FreeGroup.isReduced_cons_cons.mp hpair).1 rfl
        subst c
        refine ⟨((i,b),n+2)::R,?_,?_,hred⟩
        · simp only [expandSignedRuns,List.flatMap_cons,List.replicate_succ,List.cons_append,he]
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact hpos p (List.mem_cons_of_mem _ hp)
      · refine ⟨((i,b),1)::((j,c),n+1)::R,?_,?_,?_⟩
        · simpa [expandSignedRuns] using congrArg (List.cons (i,b)) hR
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Nat.zero_lt_one
          · exact hpos p hp
        · exact ⟨hred,hij⟩

end
section
variable {α : Type u_36} {G : Type u_37} [Group G]

def signedExponent (b : Bool) (n : ℕ) : ℤ := bif b then (n : ℤ) else -(n : ℤ)

theorem signedExponent_ne_zero (b : Bool) (n : ℕ) (hn : 0<n) : signedExponent b n≠0 := by
  cases b <;> simp [signedExponent,ne_of_gt hn]

theorem signedPower (b : Bool) (n : ℕ) (x : G) :
    x^signedExponent b n = (bif b then x else x⁻¹)^n := by
  cases b <;> simp [signedExponent]

def signedRunBlocks (R : List ((α×Bool)×ℕ)) : List (α×ℤ) :=
  R.map (fun p => (p.1.1,signedExponent p.1.2 p.2))

theorem lift_expandSignedRuns (f : α→G) (R : List ((α×Bool)×ℕ)) :
    FreeGroup.lift f (FreeGroup.mk (expandSignedRuns R))=
      ((signedRunBlocks R).map (fun p => f p.1^p.2)).prod := by
  rw [FreeGroup.lift_mk]
  induction R with
  | nil => rfl
  | cons p R ih =>
    rcases p with ⟨⟨i,b⟩,n⟩
    simpa only [expandSignedRuns,List.flatMap_cons,List.map_append,List.prod_append,
      List.map_replicate,List.prod_replicate,signedRunBlocks,List.map_cons,List.prod_cons,
      signedPower] using congrArg (fun x : G => (bif b then f i else (f i)⁻¹)^n*x) ih

end
namespace FreeFock
variable {α : Type u_38} [DecidableEq α]

def haarRepresentation : FreeGroup α →* unitary (gaussianAlgebra α) :=
  FreeGroup.lift spectralHaar

def haarOperatorRepresentation : FreeGroup α →* Operator α :=
  (gaussianAlgebra α).subtype.toMonoidHom.comp
    ((unitary (gaussianAlgebra α)).subtype.comp haarRepresentation)

 theorem haarProduct_eq_prod (L : List (α×ℤ)) :
    haarProduct L = (((L.map (fun p => (spectralHaar p.1)^p.2)).prod : unitary (gaussianAlgebra α)) : gaussianAlgebra α) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases p with ⟨i,k⟩
    change ((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) * haarProduct L = _
    change ((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) * haarProduct L =
      (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) * _
    exact congrArg (fun x : Operator α =>
      (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)*x) ih

 theorem haarRepresentation_run_moment (R : List ((α×Bool)×ℕ))
    (hpos : ∀p∈R,0<p.2) (hred : adjacentDistinct (R.map (fun p => p.1.1))) (hne : R≠[]) :
    vacuumTrace (haarOperatorRepresentation (FreeGroup.mk (expandSignedRuns R)))=0 := by
  change vacuumTrace (((FreeGroup.lift (spectralHaar (α := α)) (FreeGroup.mk (expandSignedRuns R)) : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)=0
  rw [lift_expandSignedRuns,← haarProduct_eq_prod]
  apply spectralHaar_mixed_moment
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact signedExponent_ne_zero _ _ (hpos q hq)
  · have he : ∀ L : List α, colorsReduced L=adjacentDistinct L := by
      intro L
      induction L with
      | nil => rfl
      | cons i L ih => simp only [colorsReduced,adjacentDistinct,ih]
    rw [he]
    simpa only [signedRunBlocks,List.map_map,Function.comp_def] using hred
  · simpa [signedRunBlocks] using hne

 theorem haarRepresentation_moment (g : FreeGroup α) :
    vacuumTrace (haarOperatorRepresentation g)=if g=1 then 1 else 0 := by
  classical
  by_cases hg : g=1
  · subst g
    simp only [map_one,ite_true,vacuumTrace_one]
  · rw [ite_eq_right hg]
    obtain ⟨R,hR,hpos,hred⟩ := reduced_signed_runs g.toWord FreeGroup.isReduced_toWord
    have hne : R≠[] := by
      intro he
      have hn : g.toWord=[] := by simpa only [he,expandSignedRuns,List.flatMap_nil] using hR
      apply hg
      rw [← FreeGroup.mk_toWord (x := g),hn]
      rfl
    rw [← FreeGroup.mk_toWord (x := g),hR]
    exact haarRepresentation_run_moment R hpos hred hne

end FreeFock

namespace CyclicUnitary
open scoped ENNReal
variable {G : Type u_42} {E : Type u_43} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (ρ : G →* (E →L[ℂ] E)) (hstar : ∀ g,star (ρ g)=ρ g⁻¹) (ξ : E)

omit [DecidableEq G] in
include hstar in

theorem adjoin_range_span :
    (StarAlgebra.adjoin ℂ (Set.range ρ)).toSubalgebra.toSubmodule=
      Submodule.span ℂ (Set.range ρ) := by
  rw [StarAlgebra.adjoin_eq_span]
  have hs : star (Set.range ρ)=Set.range ρ := by
    ext T
    change (star T∈Set.range ρ) ↔ T∈Set.range ρ
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [← hstar,hg,star_star]
    · rintro ⟨g,rfl⟩
      exact ⟨g⁻¹,(hstar g).symm⟩
  rw [hs,Set.union_self]
  let M : Submonoid (E →L[ℂ] E) :=
    { carrier := Set.range ρ
      one_mem' := ⟨1,map_one ρ⟩
      mul_mem' := by
        rintro _ _ ⟨g,rfl⟩ ⟨h,rfl⟩
        exact ⟨g*h,map_mul ρ g h⟩ }
  change Submodule.span ℂ ((Submonoid.closure (M : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))=_
  rw [Submonoid.closure_eq]
  rfl

def orbitSpan : Submodule ℂ E := Submodule.span ℂ (Set.range (fun g => ρ g ξ))

omit [DecidableEq G] in
include hstar in
theorem apply_mem_orbitSpan (T : (E →L[ℂ] E)) (hT : T∈StarAlgebra.adjoin ℂ (Set.range ρ)) :
    T ξ∈orbitSpan ρ ξ := by
  change T∈(StarAlgebra.adjoin ℂ (Set.range ρ)).toSubalgebra.toSubmodule at hT
  rw [adjoin_range_span ρ hstar] at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨g,rfl⟩ := hT
    exact Submodule.subset_span (Set.mem_range_self g)
  | zero => exact (orbitSpan ρ ξ).zero_mem
  | add T U _ _ hT hU => exact (orbitSpan ρ ξ).add_mem hT hU
  | smul c T _ hT => exact (orbitSpan ρ ξ).smul_mem c hT

include hstar in
theorem orbit_inner (htrace : ∀ g,inner ℂ ξ (ρ g ξ)=if g=1 then 1 else 0) (g h : G) :
    inner ℂ (ρ g ξ) (ρ h ξ)=if g=h then 1 else 0 := by
  classical
  calc
    _ = inner ℂ ξ (star (ρ g) (ρ h ξ)) :=
      (ContinuousLinearMap.adjoint_inner_right (ρ g) ξ (ρ h ξ)).symm
    _ = inner ℂ ξ (ρ (g⁻¹*h) ξ) := by rw [hstar,map_mul]; rfl
    _ = _ := by rw [htrace]; simp only [inv_mul_eq_one]

def basis (g : G) : lp (fun _ : G => ℂ) 2 := lp.single 2 g 1

omit [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
 theorem basis_inner (g h : G) :
    inner ℂ (basis g) (basis h)=if g=h then 1 else 0 := by
  simp [basis,lp.inner_single_left,lp.single_apply,Pi.single_apply]

omit [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
 theorem basis_total : (Submodule.span ℂ (Set.range (basis (G := G)))).topologicalClosure=⊤ := by
  let K := (Submodule.span ℂ (Set.range (basis (G := G)))).topologicalClosure
  apply top_unique
  intro η _
  apply (Submodule.span ℂ (Set.range (basis (G := G)))).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) η)
  filter_upwards [] with s
  apply K.sum_mem
  intro g _
  have he : lp.single (E := fun _ : G => ℂ) 2 g (η g)=(η g) • basis g := by
    ext h
    simp [basis,lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self g)))

def spatial (htrace : ∀ g,inner ℂ ξ (ρ g ξ)=if g=1 then 1 else 0)
    (htotal : (orbitSpan ρ ξ).topologicalClosure=⊤) :
    lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] E :=
  GramSpatial.spatial basis (fun g => ρ g ξ)
    (fun g h => (orbit_inner ρ hstar ξ htrace g h).trans (basis_inner g h).symm)
    basis_total htotal

theorem spatial_basis (htrace : ∀ g,inner ℂ ξ (ρ g ξ)=if g=1 then 1 else 0)
    (htotal : (orbitSpan ρ ξ).topologicalClosure=⊤) (g : G) :
    spatial ρ hstar ξ htrace htotal (basis g)=ρ g ξ :=
  GramSpatial.spatial_family _ _ _ _ _ g

end CyclicUnitary
namespace FreeFock
variable {α : Type u_44} [DecidableEq α]

 theorem haarOperatorRepresentation_star (g : FreeGroup α) :
    star (haarOperatorRepresentation g)=haarOperatorRepresentation g⁻¹ := by
  change star (((haarRepresentation g : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) =
    (((haarRepresentation g⁻¹ : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)
  rw [map_inv]
  rfl

 theorem haarOperatorRepresentation_of (i : α) :
    haarOperatorRepresentation (FreeGroup.of i)=spectralHaarOperator i := by
  change ((((FreeGroup.lift (spectralHaar (α := α))) (FreeGroup.of i) : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) = _
  rw [FreeGroup.lift_apply_of]
  rfl

 theorem haarGroup_cyclic_total :
    (CyclicUnitary.orbitSpan (haarOperatorRepresentation (α := α)) vacuum).topologicalClosure=⊤ := by
  apply top_unique
  rw [← spectralHaar_cyclic_total (α := α)]
  apply Submodule.topologicalClosure_mono
  rintro η ⟨T,hT,rfl⟩
  apply CyclicUnitary.apply_mem_orbitSpan haarOperatorRepresentation haarOperatorRepresentation_star
  apply StarAlgebra.adjoin_mono _ hT
  rintro _ ⟨i,rfl⟩
  exact ⟨FreeGroup.of i,haarOperatorRepresentation_of i⟩

def haarSpatial : lp (fun _ : FreeGroup α => ℂ) 2 ≃ₗᵢ[ℂ] Fock α :=
  CyclicUnitary.spatial haarOperatorRepresentation haarOperatorRepresentation_star vacuum
    haarRepresentation_moment haarGroup_cyclic_total

 theorem haarSpatial_basis (g : FreeGroup α) :
    haarSpatial (CyclicUnitary.basis g)=haarOperatorRepresentation g vacuum :=
  CyclicUnitary.spatial_basis _ _ _ _ _ g

 theorem haarSpatial_vacuum : haarSpatial (CyclicUnitary.basis (1 : FreeGroup α))=vacuum := by
  rw [haarSpatial_basis,map_one]
  rfl

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

theorem equiv_mem_centralizer (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (T : A) :
    e T∈StarSubalgebra.centralizer ℂ (e '' S) ↔ T∈StarSubalgebra.centralizer ℂ S := by
  simp only [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h U hU
    have h := h (e U) ⟨U,hU,rfl⟩
    constructor
    · apply (EquivLike.injective e); simpa only [map_mul] using h.1
    · apply (EquivLike.injective e); simpa only [map_mul,map_star] using h.2
  · rintro h _ ⟨U,hU,rfl⟩
    have h := h U hU
    constructor
    · simpa only [map_mul] using congrArg e h.1
    · simpa only [map_mul,map_star] using congrArg e h.2

theorem equiv_image_centralizer (e : A ≃⋆ₐ[ℂ] B) (S : Set A) :
    e '' (StarSubalgebra.centralizer ℂ S : Set A)=
      (StarSubalgebra.centralizer ℂ (e '' S) : Set B) := by
  ext T
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (equiv_mem_centralizer e S U).mpr hU
  · intro hT
    refine ⟨e.symm T,?_,e.apply_symm_apply T⟩
    apply (equiv_mem_centralizer e S _).mp
    rw [e.apply_symm_apply]
    exact hT

theorem equiv_mem_bicommutant (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (T : A) :
    e T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (e '' S) : Set B) ↔
    T∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set A) := by
  rw [← equiv_image_centralizer]
  exact equiv_mem_centralizer e _ T
def restrictStarAlgEquiv (e : A ≃⋆ₐ[ℂ] B) (S : StarSubalgebra ℂ A) (T : StarSubalgebra ℂ B)
    (he : ∀ a,e a∈T ↔ a∈S) : S ≃⋆ₐ[ℂ] T where
  toFun a := ⟨e a,(he a).mpr a.property⟩
  invFun b := ⟨e.symm b,(he _).mp (by rw [e.apply_symm_apply]; exact b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul e (a : A) (b : A))
  map_add' a b := Subtype.ext (map_add e (a : A) (b : A))
  map_smul' c a := Subtype.ext (map_smul e c (a : A))
  map_star' a := Subtype.ext (map_star e (a : A))

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

theorem leftRegular_basis (g h : G) :
    leftRegular g (CyclicUnitary.basis h)=CyclicUnitary.basis (g*h) := by
  ext k
  simp only [leftRegular_apply,CyclicUnitary.basis,lp.single_apply,Pi.single_apply]
  congr 1
  exact propext (inv_mul_eq_iff_eq_mul)

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

theorem haarSpatial_intertwines (g : FreeGroup α) :
    haarSpatial.conjStarAlgEquiv (leftRegular g)=haarOperatorRepresentation g := by
  have h : (haarSpatial (α := α)).toContinuousLinearEquiv.toContinuousLinearMap.comp (leftRegular g)=
      (haarOperatorRepresentation g).comp haarSpatial.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
    intro h
    apply ContinuousLinearMap.ext
    intro z
    have hz : lp.single (E := fun _ : FreeGroup α => ℂ) 2 h z=z • CyclicUnitary.basis h := by
      ext k
      simp [CyclicUnitary.basis,lp.single_apply,Pi.single_apply]
    change haarSpatial (leftRegular g (lp.single 2 h z))=
      haarOperatorRepresentation g (haarSpatial (lp.single 2 h z))
    rw [hz,map_smul,map_smul,map_smul,map_smul]
    congr 1
    rw [leftRegular_basis,haarSpatial_basis,haarSpatial_basis]
    exact DFunLike.congr_fun (map_mul haarOperatorRepresentation g h) vacuum
  apply ContinuousLinearMap.ext
  intro ξ
  have h := DFunLike.congr_fun h (haarSpatial.symm ξ)
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.apply_symm_apply] using h

theorem haarRepresentation_commutant :
    StarSubalgebra.centralizer ℂ (Set.range (haarOperatorRepresentation (α := α)))=
      gaussianCommutant α := by
  rw [← haar_gaussian_commutant]
  apply le_antisymm
  · apply StarSubalgebra.centralizer_le ℂ
    rintro _ ⟨i,rfl⟩
    exact ⟨FreeGroup.of i,haarOperatorRepresentation_of i⟩
  · intro C hC
    rw [haar_gaussian_commutant] at hC
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨g,rfl⟩
    have hg : haarOperatorRepresentation g∈gaussianAlgebra α :=
      (haarRepresentation g : gaussianAlgebra α).property
    exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hg C hC).1.symm,
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hg) C hC).1.symm⟩

theorem haarSpatial_mem_vonNeumann (T : GroupOperator (FreeGroup α)) :
    haarSpatial.conjStarAlgEquiv T∈gaussianAlgebra α ↔ T∈groupVonNeumann (FreeGroup α) := by
  have he : haarSpatial.conjStarAlgEquiv '' leftTranslations (FreeGroup α)=
      Set.range (haarOperatorRepresentation (α := α)) := by
    rw [leftTranslations_eq_range,← Set.range_comp]
    congr 1
    funext g
    exact haarSpatial_intertwines g
  have h := equiv_mem_bicommutant haarSpatial.conjStarAlgEquiv (leftTranslations (FreeGroup α)) T
  rw [he,haarRepresentation_commutant] at h
  exact h

def gaussianGroupIso : groupVonNeumann (FreeGroup α) ≃⋆ₐ[ℂ] gaussianAlgebra α :=
  restrictStarAlgEquiv haarSpatial.conjStarAlgEquiv _ _ haarSpatial_mem_vonNeumann

theorem gaussianGroupIso_trace (T : groupVonNeumann (FreeGroup α)) :
    vacuumTrace ((gaussianGroupIso T : gaussianAlgebra α) : Operator α)=canonicalTrace T := by
  have hcoe : ((gaussianGroupIso T : gaussianAlgebra α) : Operator α)=
      (haarSpatial (α := α)).conjStarAlgEquiv (T : GroupOperator (FreeGroup α)) := rfl
  rw [hcoe]
  unfold vacuumTrace
  rw [← haarSpatial_vacuum (α := α),LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    haarSpatial.symm_apply_apply,haarSpatial.inner_map_map]
  simp only [CyclicUnitary.basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one]
  unfold canonicalTrace
  exact congrArg (fun ξ : GroupHilbert (FreeGroup α) => ((T : GroupOperator (FreeGroup α)) ξ) 1) (by
    ext g
    simp only [lp.single_apply,Pi.single_apply]
    split_ifs <;> rfl)

@[instance_reducible] def gaussianUltraweakTopology (α : Type u_49) [DecidableEq α] :
    TopologicalSpace (gaussianAlgebra α) :=
  TopologicalSpace.induced (fun T : gaussianAlgebra α => (T : Operator α))
    (ultraweakOperatorTopology (List α))

theorem gaussianGroupIso_normal :
    @Continuous _ _ (groupUltraweakTopology (FreeGroup α)) (gaussianUltraweakTopology α)
      (gaussianGroupIso (α := α)) := by
  let : TopologicalSpace (GroupOperator (FreeGroup α)) := ultraweakOperatorTopology (FreeGroup α)
  let : TopologicalSpace (Operator α) := ultraweakOperatorTopology (List α)
  let : TopologicalSpace (groupVonNeumann (FreeGroup α)) := groupUltraweakTopology (FreeGroup α)
  let : TopologicalSpace (gaussianAlgebra α) := gaussianUltraweakTopology α
  exact ((spatial_ultraweak_continuous haarSpatial).comp continuous_subtype_val).subtype_mk _

end FreeFock

end FreeGroupFactorMain

end

end OAI

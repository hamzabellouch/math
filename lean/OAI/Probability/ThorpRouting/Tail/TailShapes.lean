import Mathlib
import OAI.Probability.ThorpRouting.Tail.InsertionPerm

namespace OAI

namespace ThorpNine.Tail

namespace Thorp.Specht
open scoped BigOperators Classical

abbrev TailShapes (N j : ℕ) := {μ : Shapes N // μ.1.card-μ.1.rowLen 0=j}

noncomputable def tailShapePartition (N j : ℕ) (μ : TailShapes N j) : Nat.Partition j where
  parts := μ.1.1.rowLens.tail
  parts_pos := fun {x} hx => μ.1.1.pos_of_mem_rowLens x (List.mem_of_mem_tail (by simpa using hx))
  parts_sum := by simpa using (rowLens_tail_sum μ.1.1).trans μ.2

lemma tailShapePartition_injective (N j : ℕ) : Function.Injective (tailShapePartition N j) := by
  intro μ ν he
  have hh : (μ.1.1.rowLens.tail : Multiset ℕ)=(ν.1.1.rowLens.tail : Multiset ℕ) :=
    congrArg Nat.Partition.parts he
  have ht : μ.1.1.rowLens.tail=ν.1.1.rowLens.tail := by
    have hm := congrArg (fun s : Multiset ℕ => s.sort (· ≥ ·)) hh
    simpa only [Multiset.coe_sort,
      List.mergeSort_eq_self _ μ.1.1.rowLens_sorted.pairwise.tail,
      List.mergeSort_eq_self _ ν.1.1.rowLens_sorted.pairwise.tail] using hm
  have hl := positive_list_eq_of_tail_sum (μ.1.1.pos_of_mem_rowLens) (ν.1.1.pos_of_mem_rowLens)
    ht (by rw [sum_rowLens,sum_rowLens,μ.1.2,ν.1.2])
  apply Subtype.ext
  apply Subtype.ext
  apply YoungDiagram.equivListRowLens.injective
  exact Subtype.ext hl

lemma tail_shapes_count (N j : ℕ) : Fintype.card (TailShapes N j)≤2^j := by
  exact (Fintype.card_le_of_injective _ (tailShapePartition_injective N j)).trans (partition_count j)

end Thorp.Specht

namespace Thorp
open scoped BigOperators Classical

lemma tail_preserving_pairSwitch (d : ℕ) (p : Equiv.Perm (Card (d+1)))
    (hp : ∀ x, Fin.tail (p x)=Fin.tail x) :
    pairSwitch (fun u => p (Fin.cons false u) 0)=p := by
  apply Equiv.ext
  intro x
  rw [←Fin.cons_self_tail x]
  generalize x 0=b
  generalize Fin.tail x=u
  apply funext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Bool.xor b (p (Fin.cons false u) 0)=p (Fin.cons b u) 0
    cases b with
    | false => simp
    | true =>
      have hn : p (Fin.cons false u) 0 ≠ p (Fin.cons true u) 0 := by
        intro he
        have hh : p (Fin.cons false u)=p (Fin.cons true u) := by
          rw [←Fin.cons_self_tail (p (Fin.cons false u)),←Fin.cons_self_tail (p (Fin.cons true u)),
            hp,hp,Fin.tail_cons,Fin.tail_cons,he]
        have hh := congrFun (p.injective hh) 0
        simp only [Fin.cons_zero] at hh
        contradiction
      cases h0 : p (Fin.cons false u) 0 <;> cases h1 : p (Fin.cons true u) 0 <;> simp_all
  · change u j=p (Fin.cons b u) j.succ
    have h := congrFun (hp (Fin.cons b u)) j
    simpa only [Fin.tail_cons,Fin.tail,Fin.cons_succ] using h.symm

lemma pairSwitch_injective (d : ℕ) : Function.Injective (pairSwitch (d := d)) := by
  intro ξ η h
  funext u
  have hh := congrArg (fun p : Equiv.Perm (Card (d+1)) => p (Fin.cons false u) 0) h
  change Bool.xor false (ξ u)=Bool.xor false (η u) at hh
  simpa only [Bool.false_xor] using hh

end Thorp
namespace Thorp.Specht
open scoped BigOperators Classical

noncomputable def pairFiberEquiv (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ) :
    (Card d → Bool) ≃ fiberGroup (fun x => Fin.tail (e.symm x)) :=
  Equiv.ofBijective (fun ξ => ⟨e.permCongr (pairSwitch ξ),by
    intro x
    simp only [Equiv.permCongr_apply,e.symm_apply_apply]
    exact Fin.tail_cons _ _⟩)
    ⟨fun ξ η h => pairSwitch_injective d (e.permCongr.injective (congrArg Subtype.val h)),by
      intro p
      let q := e.symm.permCongr p.1
      have hq : ∀ x, Fin.tail (q x)=Fin.tail x := by
        intro x
        have h := p.2 (e x)
        simpa only [q,Equiv.permCongr_apply,Equiv.symm_symm,e.symm_apply_apply] using h
      refine ⟨fun u => q (Fin.cons false u) 0,?_⟩
      apply Subtype.ext
      change e.permCongr (pairSwitch (fun u => q (Fin.cons false u) 0))=p.1
      rw [tail_preserving_pairSwitch d q hq]
      apply Equiv.ext
      intro x
      simp only [q,Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]⟩

lemma pair_sum_taboid_zero (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ)
    (hj : 2^d < μ.colLen 0) (v : space μ) :
    (∑ ξ : Card d → Bool, tabloidRep μ (e.permCongr (pairSwitch ξ))) v.1=0 := by
  have he : (∑ ξ : Card d → Bool, tabloidRep μ (e.permCongr (pairSwitch ξ)))=
      symmetrizer (fiberGroup (fun x => Fin.tail (e.symm x))) (tabloidRep μ) :=
    Fintype.sum_equiv (pairFiberEquiv d μ e) _ _ (fun _ => rfl)
  rw [he]
  exact tall_column_average_zero μ _ 0 (by simpa only [card_positions] using hj) v.1 v.2

lemma pair_operator_tall_zero (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ)
    (hj : 2^d < μ.colLen 0) :
    UnitaryFinite.sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) pairSwitch=0 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (spaceHilbertEquiv μ).surjective v
  have hh : (∑ ξ : Card d → Bool, representation μ (e.permCongr (pairSwitch ξ))) w=0 := by
    apply Subtype.ext
    simp only [LinearMap.sum_apply,Submodule.coe_sum,Submodule.coe_zero]
    change (∑ ξ : Card d → Bool, tabloidRep μ (e.permCongr (pairSwitch ξ)) w.1)=0
    simpa only [LinearMap.sum_apply] using pair_sum_taboid_zero d μ e hj w
  have hh' := congrArg (spaceHilbertEquiv μ) hh
  simp only [LinearMap.sum_apply,map_sum,map_zero] at hh'
  change ((Fintype.card (Card d → Bool):ℂ)⁻¹ •
    ∑ ξ : Card d → Bool, UnitaryFinite.continuousRepresentation (relabelledUnitary μ e) (pairSwitch ξ))
      (spaceHilbertEquiv μ w)=0
  rw [smul_apply,sum_apply]
  change (Fintype.card (Card d → Bool):ℂ)⁻¹ •
    (∑ ξ : Card d → Bool, spaceHilbertEquiv μ (representation μ (e.permCongr (pairSwitch ξ))
      ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ w))))=0
  simp only [LinearEquiv.symm_apply_apply,hh',smul_zero]

open UnitaryFinite

lemma palindrome_tall_zero (d : ℕ) (μ : YoungDiagram) (e : Card (d+1) ≃ Cell μ)
    (hj : 2^d<μ.colLen 0) :
    sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm (d+1))=0 := by
  let ρ := relabelledUnitary μ e
  let : NormedAddCommGroup (hilbertSpace μ) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance
  have hpair : sampleOperator (V := hilbertSpace μ) ρ (pairSwitch (d := d))=0 := pair_operator_tall_zero d μ e hj
  have hi : sampleOperator ρ (fun ω => (butterflyPerm (d+1) (decodeButterfly (d+1) ω))⁻¹)=0 := by
    rw [inverse_butterfly_average_step,hpair,mul_zero]
  rw [sampleOperator_inv ρ (relabelledUnitary_unitary μ e)] at hi
  rw [sampleOperator_palindrome _ _ (relabelledUnitary_unitary μ e),hi,mul_zero]

lemma palindrome_tall_zero_general (d : ℕ) (hd : 0<d) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
    (hj : (μ.card:ℝ)/2<(μ.colLen 0:ℝ)) :
    sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)=0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
  apply palindrome_tall_zero r μ e
  have hc : μ.card=2^(r+1) := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  rw [hc,Nat.cast_pow,Nat.cast_ofNat,pow_succ] at hj
  have hh : (2:ℝ)^r<(μ.colLen 0:ℝ) := by linarith
  exact_mod_cast hh

end Thorp.Specht

namespace Thorp.DimensionEstimates
open Filter

lemma twopow_tendsto : Tendsto (fun d : ℕ => (2:ℝ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_nat_tendsto : Tendsto (fun d : ℕ => (2:ℕ)^d) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

lemma twopow_mul_eventually (c : ℝ) (hc : 0<c) (B : ℝ) :
    ∀ᶠ d : ℕ in atTop, B≤c*(2:ℝ)^d := by
  filter_upwards [twopow_tendsto.eventually (eventually_ge_atTop (B/c))] with d hd
  exact (div_le_iff₀ hc).mp hd |>.trans_eq (mul_comm _ _)

lemma exp_two_absorb (β n : ℝ) (hx : Real.log 2≤β*n/2) :
    Real.exp (-β*n)+Real.exp (-β*n)≤Real.exp (-β*n/2) := by
  calc
    _ = Real.exp (Real.log 2-β*n) := by rw [Real.exp_sub,Real.exp_log (by norm_num)]; rw [neg_mul,Real.exp_neg]; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Thorp.DimensionEstimates
namespace Thorp.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

theorem exponential_dimension_spectral (h : ℝ) (hh : 0<h) :
    ∃ a : ℝ, 0<a ∧ ∀ᶠ d : ℕ in atTop, ∀ (μ : YoungDiagram) (e : Card d ≃ Cell μ),
      h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ)) →
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
        Real.exp (-a*Real.log (Module.finrank ℂ (space μ))) := by
  obtain ⟨L,hL,ε,t,hε,_,ht,hcount,hM⟩ := medium_parameters h hh
  obtain ⟨R,hR⟩ := eventually_atTop.mp hM
  let A := 4000*densityConstant+1
  have hA : 0<A := by dsimp [A]; have := densityConstant_pos; positivity
  let β := min (-Real.log (blockGap L)*ε/(2:ℝ)^L) (h/16000)
  have hβ : 0<β := by
    apply lt_min
    · exact div_pos (mul_pos (neg_pos.mpr (Real.log_neg (blockGap_pos L) (blockGap_lt_one L))) hε) (by positivity)
    · positivity
  let a := min (1/8000:ℝ) (β/(2*A))
  have ha : 0<a := lt_min (by norm_num) (div_pos hβ (by positivity))
  refine ⟨a,ha,?_⟩
  filter_upwards [eventually_ge_atTop (L+R),twopow_mul_eventually h hh (8000*Real.log 2),
    twopow_mul_eventually (β/2) (by positivity) (Real.log 2)] with d hd hl hb
  intro μ e hdim
  let : NormedAddCommGroup (hilbertSpace μ) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance
  let := relabelledUnitary_irreducible μ e
  have hpos : 0<Module.finrank ℂ (hilbertSpace μ) := by rw [finrank_hilbertSpace]; exact dimension_pos μ
  have hlarge : 8000*Real.log 2≤Real.log (Module.finrank ℂ (hilbertSpace μ)) := by rw [finrank_hilbertSpace]; exact hl.trans hdim
  have hlog : 0≤Real.log (Module.finrank ℂ (space μ)) := (by positivity : (0:ℝ)≤h*(2:ℝ)^d).trans hdim
  by_cases hhigh : A*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ))
  · have hden : densityConstant*(2:ℝ)^d≤Real.log (Module.finrank ℂ (hilbertSpace μ))/4000 := by
      rw [finrank_hilbertSpace]
      dsimp [A] at hhigh
      nlinarith [pow_pos (by norm_num : (0:ℝ)<2) d]
    have hspec := @full_palindrome_decay (hilbertSpace μ) _ _ _ d (relabelledUnitary μ e)
      inferInstance (relabelledUnitary_unitary μ e) hpos hden hlarge
    rw [finrank_hilbertSpace] at hspec
    apply hspec.trans (Real.exp_le_exp.mpr ?_)
    have := min_le_left (1/8000:ℝ) (β/(2*A))
    nlinarith
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (show L≤d by omega)
    have hr : R≤r := by omega
    have hdim' : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ (hilbertSpace μ)) := by rwa [finrank_hilbertSpace]
    have hs := @medium_exception_decay (hilbertSpace μ) _ _ _ L r h ε t ht hcount
      (relabelledUnitary μ e) inferInstance (relabelledUnitary_unitary μ e) hpos hdim' hlarge (hR r hr)
    have hb1 : Real.log (blockGap L)*ε*(2:ℝ)^r≤-β*(2:ℝ)^(L+r) := by
      have hb0 := min_le_left (-Real.log (blockGap L)*ε/(2:ℝ)^L) (h/16000)
      have hp := (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^L)).mp hb0
      have hp := mul_le_mul_of_nonneg_right hp (by positivity : (0:ℝ)≤(2:ℝ)^r)
      rw [pow_add]
      dsimp [β]
      nlinarith
    have hb2 : -h*(2:ℝ)^(L+r)/16000≤-β*(2:ℝ)^(L+r) := by
      have hp := mul_le_mul_of_nonneg_right (min_le_right (-Real.log (blockGap L)*ε/(2:ℝ)^L) (h/16000))
        (by positivity : (0:ℝ)≤(2:ℝ)^(L+r))
      dsimp [β]
      linarith
    apply hs.trans ((add_le_add (Real.exp_le_exp.mpr hb1) (Real.exp_le_exp.mpr hb2)).trans ?_)
    apply (exp_two_absorb β ((2:ℝ)^(L+r)) (by nlinarith)).trans
    apply Real.exp_le_exp.mpr
    have hdmax := le_of_not_ge hhigh
    have hp := mul_le_mul_of_nonneg_left hdmax (by positivity : 0≤β/(2*A))
    have he : β/(2*A)*(A*(2:ℝ)^(L+r))=β*(2:ℝ)^(L+r)/2 := by field_simp
    rw [he] at hp
    have hba := mul_le_mul_of_nonneg_right (min_le_right (1/8000:ℝ) (β/(2*A))) hlog
    dsimp [a] at *
    linarith


theorem spectral_regimes :
    ∃ a h : ℝ, 0<a ∧ 0<h ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (μ : YoungDiagram) (e : Card d ≃ Cell μ), 0<μ.card-μ.rowLen 0 →
        (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2 →
        ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖≤
          Real.exp (-a*Real.log (Module.finrank ℂ (space μ))) ∧
        1≤Real.log (Module.finrank ℂ (space μ)) ∧
        (((1/2:ℝ)*Real.log μ.card≤Real.log (Module.finrank ℂ (space μ)) ∧
          (μ.card-μ.rowLen 0:ℕ)≤Real.log (Module.finrank ℂ (space μ))) ∨
          h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ))) := by
  obtain ⟨X,hX,hnear⟩ := near_row_spectral
  have hXpos : 0<X := by linarith
  have hδ : 0<(1:ℝ)/X := by positivity
  have hδ2 : (1:ℝ)/X≤1/2 := (div_le_iff₀ hXpos).mpr (by linarith)
  obtain ⟨h,hh,hmedium⟩ := medium_dimension (1/X) hδ hδ2
  obtain ⟨a₀,ha₀,hlarge⟩ := exponential_dimension_spectral h hh
  let a := min (nearFraction/8000) a₀
  have ha : 0<a := lt_min (by norm_num [nearFraction]) ha₀
  refine ⟨a,h,ha,hh,?_⟩
  have hl := (Real.tendsto_log_atTop.comp twopow_tendsto).eventually
    (eventually_ge_atTop (2*max (32768000*Real.log 2) 1))
  filter_upwards [hlarge,twopow_nat_tendsto.eventually hmedium,hl,
    twopow_mul_eventually h hh 1] with d hspec hdim hlog h1
  intro μ e hj hc
  simp only [Function.comp_apply] at hlog
  have hcard : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  have hcardR : (μ.card:ℝ)=(2:ℝ)^d := by exact_mod_cast hcard
  have hμlog : max (32768000*Real.log 2) 1≤(1/2:ℝ)*Real.log μ.card := by rw [hcardR]; linarith
  by_cases hx : X≤(μ.card:ℝ)/(μ.card-μ.rowLen 0:ℕ)
  · obtain ⟨hs,hl,hjD⟩ := hnear d μ e hj hx ((le_max_left _ _).trans hμlog)
    have h1D : 1≤Real.log (Module.finrank ℂ (space μ)) := ((le_max_right _ _).trans hμlog).trans hl
    refine ⟨hs.trans (Real.exp_le_exp.mpr ?_),h1D,Or.inl ⟨hl,hjD⟩⟩
    have hp := mul_le_mul_of_nonneg_right (min_le_left (nearFraction/8000) a₀) (by linarith : 0≤Real.log (Module.finrank ℂ (space μ)))
    dsimp [a]
    linarith
  · have htail : (1/X)*(μ.card:ℝ)≤(μ.card:ℝ)-μ.rowLen 0 := by
      have hjR : (0:ℝ)<(μ.card-μ.rowLen 0:ℕ) := by exact_mod_cast hj
      have hh := (div_lt_iff₀ hjR).mp (lt_of_not_ge hx)
      have hs : ((μ.card-μ.rowLen 0:ℕ):ℝ)=(μ.card:ℝ)-μ.rowLen 0 := by
        rw [Nat.cast_sub (rowLen_zero_le_card μ)]
      rw [hs] at hh
      have hd : (μ.card:ℝ)/X≤(μ.card:ℝ)-μ.rowLen 0 :=
        (div_le_iff₀ hXpos).mpr (by nlinarith)
      convert hd using 1; ring
    have hdim' : h*(2:ℝ)^d≤Real.log (Module.finrank ℂ (space μ)) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using
        hdim μ hcard (by simpa only [hcard] using htail) (by simpa only [hcard] using hc)
    have h1D := h1.trans hdim'
    refine ⟨(hspec μ e hdim').trans (Real.exp_le_exp.mpr ?_),h1D,Or.inr hdim'⟩
    have hp := mul_le_mul_of_nonneg_right (min_le_right (nearFraction/8000) a₀) (by linarith : 0≤Real.log (Module.finrank ℂ (space μ)))
    dsimp [a]
    linarith

end Thorp.Specht

namespace Thorp.StrongSmoothing

noncomputable def regularAbsoluteEvenTrace (d : ℕ) (order : Equiv.Perm (Fin d)) (u : ℕ) : ℝ :=
  Matrix.trace ((reflectedKernel d (2^d) order false)^u)

def MainStatement : Prop :=
  ∃ u : ℕ, 1 ≤ u ∧ ∃ C : ℝ,
    (∀ d l : ℕ, l ≤ 2^d → ∀ order : Equiv.Perm (Fin d), ∀ orientation : Bool,
      ∀ x y : Tuples d l,
        ((reflectedKernel d l order orientation)^u) x y ≤
          Real.exp (C*l)/((2^d).descFactorial l:ℝ)) ∧
    (∀ d : ℕ, ∀ order : Equiv.Perm (Fin d),
      regularAbsoluteEvenTrace d order u ≤ Real.exp (C*(2:ℝ)^d))


open scoped BigOperators

variable {X : Type*} [Fintype X] [Nonempty X]

omit [Nonempty X] in
lemma mean_nonneg (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteMean f :=
  finiteMean_nonneg hf

lemma mean_rpow_concave (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    finiteMean (fun x => (f x)^a) ≤ (finiteMean f)^a := by
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hh := (Real.concaveOn_rpow ha ha1).le_map_sum
    (t := Finset.univ) (w := fun _ : X => 1/(Fintype.card X:ℝ))
    (p := f) (fun _ _ => by positivity)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp)
    (fun x _ => hf x)
  simpa only [smul_eq_mul,one_div,←Finset.mul_sum,mul_comm _ (∑ _ : X,_),
    ←div_eq_mul_inv,finiteMean] using hh

noncomputable def act (K : Matrix X X ℝ) (f : X → ℝ) (y : X) : ℝ := ∑ x, K x y*f x

omit [Nonempty X] in
lemma act_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : X) : 0 ≤ act K f y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hK x y) (hf x))

omit [Nonempty X] in
lemma act_rpow_le (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y = 1) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {b : ℝ} (hb : 1 ≤ b) (y : X) :
    (act K f y)^b ≤ act K (fun x => (f x)^b) y := by
  simpa only [smul_eq_mul,act] using
    (convexOn_rpow hb).map_sum_le (t := Finset.univ) (w := fun x => K x y)
      (p := f) (fun x _ => hK x y) (hcol y) (fun x _ => hf x)

lemma act_one_to_p (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    {p A : ℝ} (hp : 1 ≤ p)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun y => (act K f y)^p) ≤ Real.exp A*(finiteMean f)^p := by
  classical
  let s : ℝ := ∑ x, f x
  have hs : 0 ≤ s := Finset.sum_nonneg (fun x _ => hf x)
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hz : s=0
  · have hfz : ∀ x, f x=0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hf x)).mp hz x (Finset.mem_univ _)
    simp only [act,hfz,mul_zero,Finset.sum_const_zero,finiteMean,zero_div,
      Real.zero_rpow (show p ≠ 0 by linarith),mul_zero,le_refl]
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    let w : X → ℝ := fun x => f x/s
    have hw : ∀ x, 0 ≤ w x := fun x => div_nonneg (hf x) hs
    have hws : ∑ x, w x = 1 := by simp only [w,←Finset.sum_div]; exact div_self hz
    have hact (y : X) : act K f y = finiteMean f * ∑ x, w x*((Fintype.card X:ℝ)*K x y) := by
      simp only [act,w,finiteMean,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hz' : (∑ x, f x) ≠ 0 := hz
      dsimp [s]
      field_simp [hz',ne_of_gt hN]
    have hj (y : X) : (act K f y)^p ≤ (finiteMean f)^p*
        ∑ x, w x*((Fintype.card X:ℝ)*K x y)^p := by
      rw [hact,Real.mul_rpow (mean_nonneg f hf)
        (Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (mul_nonneg hN.le (hK x y))))]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (mean_nonneg f hf) _)
      exact (convexOn_rpow hp).map_sum_le
        (fun x _ => hw x) hws (fun x _ => mul_nonneg hN.le (hK x y))
    have hh := finiteMean_mono hj
    have he : finiteMean (fun y => (finiteMean f)^p*
        ∑ x, w x*((Fintype.card X:ℝ)*K x y)^p) =
        (finiteMean f)^p * ∑ x, w x*finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) := by
      simp_rw [mul_comm ((finiteMean f)^p), finiteMean_mul_const,
        finiteMean_sum, mul_comm (w _), finiteMean_mul_const]
    rw [he] at hh
    apply hh.trans
    have hsum : (∑ x, w x*finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p)) ≤ Real.exp A := by
      calc
        _ ≤ ∑ x, w x*Real.exp A := Finset.sum_le_sum
          (fun x _ => mul_le_mul_of_nonneg_left (hm x) (hw x))
        _ = Real.exp A := by rw [←Finset.sum_mul,hws,one_mul]
    simpa only [mul_comm (Real.exp A)] using
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (mean_nonneg f hf) _)

lemma act_b_to_pb (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∑ x, K x y = 1) {p A b : ℝ} (hp : 1 ≤ p) (hb : 1 ≤ b)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun y => (act K f y)^(b*p)) ≤
      Real.exp A*(finiteMean (fun x => (f x)^b))^p := by
  calc
    _ ≤ finiteMean (fun y => (act K (fun x => (f x)^b) y)^p) := by
      apply finiteMean_mono
      intro y
      rw [Real.rpow_mul (act_nonneg K hK f hf y)]
      exact Real.rpow_le_rpow (Real.rpow_nonneg (act_nonneg K hK f hf y) _) (act_rpow_le K hK hcol f hf hb y) (by linarith)
    _ ≤ _ := act_one_to_p K hK hp hm _ (fun x => Real.rpow_nonneg (hf x) _)

variable [DecidableEq X]

omit [Nonempty X] in
lemma kernel_pow_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (r : ℕ) :
    ∀ x y, 0 ≤ (K^r) x y := by
  classical
  induction r with
  | zero => intro x y; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ r ih =>
    intro x y
    rw [pow_succ,Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hK z y))

omit [Nonempty X] in
lemma kernel_pow_row (K : Matrix X X ℝ) (hrow : ∀ x, ∑ y, K x y = 1) (r : ℕ) :
    ∀ x, ∑ y, (K^r) x y = 1 := by
  classical
  induction r with
  | zero => intro x; simp [Matrix.one_apply]
  | succ r ih =>
    intro x
    simp only [pow_succ,Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,hrow,mul_one,ih]

noncomputable def rowDensity (K : Matrix X X ℝ) (r : ℕ) (x y : X) : ℝ :=
  (Fintype.card X:ℝ)*(K^r) x y

omit [Nonempty X] in
lemma rowDensity_nonneg (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y) (r : ℕ) (x y : X) :
    0 ≤ rowDensity K r x y := mul_nonneg (Nat.cast_nonneg _) (kernel_pow_nonneg K hK r x y)

omit [Nonempty X] in
lemma rowDensity_succ (K : Matrix X X ℝ) (r : ℕ) (x y : X) :
    rowDensity K (r+1) x y = act K (rowDensity K r x) y := by
  simp only [rowDensity,pow_succ,Matrix.mul_apply,act,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma rowDensity_mean (K : Matrix X X ℝ) (hrow : ∀ x, ∑ y, K x y = 1) (r : ℕ) (x : X) :
    finiteMean (rowDensity K r x) = 1 := by
  have hN : (Fintype.card X:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [finiteMean,rowDensity,←Finset.mul_sum,kernel_pow_row K hrow,mul_one,div_self hN]

lemma rowDensity_moment_iter (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (x : X) :
    finiteMean (fun y => (rowDensity K r x y)^(p^r)) ≤ Real.exp (A*r*p^r) := by
  induction r with
  | zero => simp [rowDensity_mean K hrow]
  | succ r ih =>
    have hpr : 1 ≤ p^r := one_le_pow₀ hp
    have hps : 1 ≤ p^(r+1) := one_le_pow₀ hp
    simp_rw [rowDensity_succ]
    calc
      _ ≤ Real.exp A*(finiteMean (fun y => (rowDensity K r x y)^(p^r)))^p := by
        rw [pow_succ]
        exact act_b_to_pb K hK hcol hp hpr hm _ (rowDensity_nonneg K hK r x)
      _ ≤ Real.exp A*(Real.exp (A*r*p^r))^p := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Real.rpow_le_rpow (mean_nonneg _ (fun y => Real.rpow_nonneg
          (rowDensity_nonneg K hK r x y) _)) ih (le_trans zero_le_one hp)
      _ = Real.exp (A+A*r*p^(r+1)) := by rw [←Real.exp_mul,←Real.exp_add,pow_succ]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hps hA
        push_cast
        nlinarith

lemma rowDensity_second_moment (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (hr : 2 ≤ p^r) (x : X) :
    finiteMean (fun y => (rowDensity K r x y)^2) ≤ Real.exp (2*A*r) := by
  have hpos : 0 < p^r := by linarith
  have hj := mean_rpow_concave (fun y => (rowDensity K r x y)^(p^r))
    (fun y => Real.rpow_nonneg (rowDensity_nonneg K hK r x y) _)
    (a := 2/(p^r)) (by positivity) ((div_le_one hpos).mpr hr)
  have he (y : X) : ((rowDensity K r x y)^(p^r))^(2/(p^r)) = (rowDensity K r x y)^2 := by
    rw [←Real.rpow_mul (rowDensity_nonneg K hK r x y)]
    rw [mul_div_cancel₀ _ (ne_of_gt hpos),Real.rpow_two]
  simp_rw [he] at hj
  apply hj.trans
  calc
    _ ≤ (Real.exp (A*r*p^r))^(2/(p^r)) :=
      Real.rpow_le_rpow (mean_nonneg _ (fun y => Real.rpow_nonneg
        (rowDensity_nonneg K hK r x y) _)) (rowDensity_moment_iter K hK hrow hcol hp hA hm r x)
        (by positivity)
    _ = _ := by rw [←Real.exp_mul]; congr 1; field_simp [ne_of_gt hpos]

lemma symmetric_kernel_smoothing (K : Matrix X X ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hcol : ∀ y, ∑ x, K x y = 1)
    (hsym : K.IsSymm) {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (hm : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*K x y)^p) ≤ Real.exp A)
    (r : ℕ) (hr : 2 ≤ p^r) (x y : X) :
    (K^(2*r)) x y ≤ Real.exp (2*A*r)/(Fintype.card X:ℝ) := by
  have hN : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hs : ∀ z, (K^r) z y = (K^r) y z := fun z => (hsym.pow r).apply y z
  have he : (Fintype.card X:ℝ)*(K^(2*r)) x y =
      finiteMean (fun z => rowDensity K r x z*rowDensity K r y z) := by
    simp only [finiteMean,rowDensity,two_mul,pow_add,Matrix.mul_apply,hs,Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    field_simp
  have hh : finiteMean (fun z => rowDensity K r x z*rowDensity K r y z) ≤
      Real.exp (2*A*r) := by
    calc
      _ ≤ finiteMean (fun z => ((rowDensity K r x z)^2+(rowDensity K r y z)^2)/2) := by
        apply finiteMean_mono
        intro z
        nlinarith [sq_nonneg (rowDensity K r x z-rowDensity K r y z)]
      _ = (finiteMean (fun z => (rowDensity K r x z)^2)+
          finiteMean (fun z => (rowDensity K r y z)^2))/2 := by
        simp only [div_eq_mul_inv,finiteMean_mul_const,finiteMean_add]
      _ ≤ _ := by
        have hx := rowDensity_second_moment K hK hrow hcol hp hA hm r hr x
        have hy := rowDensity_second_moment K hK hrow hcol hp hA hm r hr y
        linarith
  apply (le_div_iff₀ hN).mpr
  simpa only [←he,mul_comm (Fintype.card X:ℝ)] using hh

lemma density_exponent_numeric : 2 ≤ (1+(1/1000:ℝ))^(1000:ℕ) := by
  calc
    (2:ℝ) = 1+(1000:ℝ)*(1/1000) := by norm_num
    _ ≤ _ := by simpa only [Nat.cast_ofNat] using
      (one_add_mul_le_pow (a := (1/1000:ℝ)) (by norm_num) 1000)

end Thorp.StrongSmoothing

namespace Thorp.StrongSmoothing.PermLaw
open scoped BigOperators
variable {X Ω Ω' : Type*} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype Ω']

noncomputable def kernel (P : Ω → Equiv.Perm X) : Matrix X X ℝ :=
  fun x y => finiteMean (fun ω => if P ω x = y then (1:ℝ) else 0)

omit [Fintype X] in
lemma nonneg (P : Ω → Equiv.Perm X) (x y : X) : 0 ≤ kernel P x y := by
  exact finiteMean_nonneg (fun ω => by split_ifs <;> norm_num)

lemma row [Nonempty Ω] (P : Ω → Equiv.Perm X) (x : X) : ∑ y, kernel P x y = 1 := by
  simp only [kernel,←finiteMean_sum]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

omit [Fintype X] in
lemma inverse (P : Ω → Equiv.Perm X) : kernel (fun ω => (P ω)⁻¹) = (kernel P).transpose := by
  ext x y
  apply finiteMean_congr
  intro ω
  have he : (P ω)⁻¹ x=y ↔ P ω y=x := by
    change (P ω).symm x=y ↔ P ω y=x
    exact (Equiv.symm_apply_eq (P ω)).trans eq_comm
  simp only [he]

lemma col [Nonempty Ω] (P : Ω → Equiv.Perm X) (y : X) : ∑ x, kernel P x y = 1 := by
  have hh := row (fun ω => (P ω)⁻¹) y
  rw [inverse] at hh
  exact hh

lemma mul (P : Ω → Equiv.Perm X) (Q : Ω' → Equiv.Perm X) :
    kernel (fun ω : Ω × Ω' => P ω.1*Q ω.2) = kernel Q*kernel P := by
  ext x y
  simp only [Matrix.mul_apply,kernel]
  have he (ω : Ω × Ω') :
      (if (P ω.1*Q ω.2) x=y then (1:ℝ) else 0) =
        ∑ z : X, (if P ω.1 z=y then (1:ℝ) else 0)*(if Q ω.2 x=z then (1:ℝ) else 0) := by
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    rfl
  change finiteMean (fun ω : Ω × Ω' => if (P ω.1*Q ω.2) x=y then (1:ℝ) else 0) = _
  simp_rw [he]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (finiteMean_prod_mul (fun ω : Ω => if P ω z=y then (1:ℝ) else 0)
    (fun ω : Ω' => if Q ω x=z then (1:ℝ) else 0)).trans (mul_comm _ _)

omit [Fintype X] in
lemma conjugate (P : Ω → Equiv.Perm X) (e : Equiv.Perm X) (x y : X) :
    kernel (fun ω => e*P ω*e⁻¹) x y = kernel P (e.symm x) (e.symm y) := by
  apply finiteMean_congr
  intro ω
  have he : (e*P ω*e⁻¹) x=y ↔ P ω (e.symm x)=e.symm y := by
    change e (P ω (e.symm x))=y ↔ _
    exact (Equiv.eq_symm_apply e).symm
  simp only [he]

end Thorp.StrongSmoothing.PermLaw

namespace Thorp.StrongSmoothing
open scoped BigOperators

section MatrixHelpers
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
lemma mul_nonneg_entries (A B : Matrix X X ℝ) (hA : ∀ x y, 0 ≤ A x y)
    (hB : ∀ x y, 0 ≤ B x y) (x y : X) : 0 ≤ (A*B) x y :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (hA x z) (hB z y))

omit [DecidableEq X] in
lemma mul_row (A B : Matrix X X ℝ) (hA : ∀ x, ∑ y, A x y = 1)
    (hB : ∀ x, ∑ y, B x y = 1) (x : X) : ∑ y, (A*B) x y = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,hB,mul_one,hA]

omit [DecidableEq X] in
lemma mul_col (A B : Matrix X X ℝ) (hA : ∀ y, ∑ x, A x y = 1)
    (hB : ∀ y, ∑ x, B x y = 1) (y : X) : ∑ x, (A*B) x y = 1 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,hA,one_mul,hB]

omit [DecidableEq X] in
lemma bound_mul_left (A B : Matrix X X ℝ) (hA : ∀ x y, 0 ≤ A x y)
    (hrow : ∀ x, ∑ y, A x y = 1) {D : ℝ} (hB : ∀ x y, B x y ≤ D) :
    ∀ x y, (A*B) x y ≤ D := by
  intro x y
  calc
    _ ≤ ∑ z, A x z*D := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hB z y) (hA x z))
    _ = D := by rw [←Finset.sum_mul,hrow,one_mul]

omit [DecidableEq X] in
lemma bound_mul_right (A B : Matrix X X ℝ) (hB : ∀ x y, 0 ≤ B x y)
    (hcol : ∀ y, ∑ x, B x y = 1) {D : ℝ} (hA : ∀ x y, A x y ≤ D) :
    ∀ x y, (A*B) x y ≤ D := by
  intro x y
  calc
    _ ≤ ∑ z, D*B z y := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (hA x z) (hB z y))
    _ = D := by rw [←Finset.mul_sum,hcol,mul_one]

lemma sandwich_power (A B : Matrix X X ℝ) (r : ℕ) : A*(B*A)^r*B = (A*B)^(r+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ = (A*(B*A)^r*B)*(A*B) := by rw [pow_succ]; noncomm_ring
      _ = (A*B)^(r+1)*(A*B) := by rw [ih]
      _ = _ := (pow_succ (A*B) (r+1)).symm

end MatrixHelpers

section TupleAction
variable {ι β Ω : Type*} [Fintype ι] [Fintype β] [DecidableEq β] [Fintype Ω]

def tuplePerm (P : Equiv.Perm β) : Equiv.Perm (ι ↪ β) where
  toFun x := x.trans P.toEmbedding
  invFun x := x.trans P.symm.toEmbedding
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

omit [Fintype ι] [Fintype β] [DecidableEq β] in
@[simp] lemma tuplePerm_apply (P : Equiv.Perm β) (x : ι ↪ β) (i : ι) :
    tuplePerm P x i = P (x i) := rfl

omit [Fintype ι] [Fintype β] [DecidableEq β] in
lemma tuplePerm_mul (P Q : Equiv.Perm β) :
    tuplePerm (ι := ι) (P*Q) = tuplePerm P*tuplePerm Q := by
  ext x i
  rfl

omit [Fintype ι] [Fintype β] [DecidableEq β] in
lemma tuplePerm_inverse (P : Equiv.Perm β) :
    tuplePerm (ι := ι) P⁻¹ = (tuplePerm P)⁻¹ := by
  ext x i
  rfl

omit [Fintype β] in
lemma tupleProbability_kernel (P : Ω → Equiv.Perm β) (x y : ι ↪ β) :
    PairRouting.tupleProbability P x y = PermLaw.kernel (fun ω => tuplePerm (P ω)) x y := by
  classical
  apply finiteMean_congr
  intro ω
  have he : (∀ i, P ω (x i) = y i) ↔ tuplePerm (P ω) x = y := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congrArg (fun z : ι ↪ β => z i) h
  simp only [he]
end TupleAction

lemma sweepKernel_law (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    sweepKernel d l order = PermLaw.kernel (fun ω => tuplePerm (ι := Fin l) (sweep d order ω)) := by
  ext x y
  exact tupleProbability_kernel _ x y

lemma reflectedKernel_conjugate (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    reflectedKernel d l order false x y =
      PairRouting.tupleProbability (palindromePerm d)
        ((tuplePerm (coordinateRelabel d order)).symm x)
        ((tuplePerm (coordinateRelabel d order)).symm y) := by
  classical
  let e : Equiv.Perm (Tuples d l) := tuplePerm (coordinateRelabel d order)
  let P := fun ω => tuplePerm (ι := Fin l) (butterflyPerm d (decodeButterfly d ω))
  have hA : sweepKernel d l order = PermLaw.kernel (fun ω => e*P ω*e⁻¹) := by
    rw [sweepKernel_law]
    simp only [sweep,tuplePerm_mul,tuplePerm_inverse]
    rfl
  rw [reflectedKernel,ite_eq_right Bool.false_ne_true,hA]
  rw [←PermLaw.inverse,←PermLaw.mul]
  have hprod : (fun ω : BenesCoins d => (e*P ω.1*e⁻¹)*((e*P ω.2*e⁻¹)⁻¹)) =
      fun ω : BenesCoins d => e*tuplePerm (ι := Fin l) (palindromePerm d ω)*e⁻¹ := by
    funext ω
    simp only [mul_inv_rev,inv_inv,palindromePerm,tuplePerm_mul]
    change (e*P ω.1*e⁻¹)*(e*(P ω.2)⁻¹*e⁻¹) = e*(P ω.1*(P ω.2)⁻¹)*e⁻¹
    group
  rw [hprod,PermLaw.conjugate,tupleProbability_kernel]


lemma sweepKernel_nonneg (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    0 ≤ sweepKernel d l order x y := PairRouting.tupleProbability_nonneg _ _ _

lemma sweepKernel_row (d l : ℕ) (order : Equiv.Perm (Fin d)) (x : Tuples d l) :
    ∑ y, sweepKernel d l order x y = 1 := by
  rw [sweepKernel_law]
  exact PermLaw.row _ _

lemma sweepKernel_col (d l : ℕ) (order : Equiv.Perm (Fin d)) (y : Tuples d l) :
    ∑ x, sweepKernel d l order x y = 1 := by
  rw [sweepKernel_law]
  exact PermLaw.col _ _

lemma reflected_nonneg (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    0 ≤ reflectedKernel d l order false x y := by
  exact mul_nonneg_entries _ _ (fun x y => sweepKernel_nonneg d l order y x)
    (sweepKernel_nonneg d l order) x y

lemma reflected_row (d l : ℕ) (order : Equiv.Perm (Fin d)) (x : Tuples d l) :
    ∑ y, reflectedKernel d l order false x y = 1 :=
  mul_row _ _ (sweepKernel_col d l order) (sweepKernel_row d l order) x

lemma reflected_col (d l : ℕ) (order : Equiv.Perm (Fin d)) (y : Tuples d l) :
    ∑ x, reflectedKernel d l order false x y = 1 :=
  mul_col _ _ (sweepKernel_row d l order) (sweepKernel_col d l order) y

lemma reflected_symmetric (d l : ℕ) (order : Equiv.Perm (Fin d)) :
    (reflectedKernel d l order false).IsSymm := Matrix.isSymm_transpose_mul_self _

lemma reflected_moment (d l : ℕ) (order : Equiv.Perm (Fin d)) (x : Tuples d l) :
    finiteMean (fun y : Tuples d l =>
      ((Fintype.card (Tuples d l):ℝ)*reflectedKernel d l order false x y)^(1+(1/1000:ℝ))) ≤
      Real.exp (l*(1+heightDecay 1)) := by
  classical
  let e : Equiv.Perm (Tuples d l) := tuplePerm (coordinateRelabel d order)
  simp_rw [reflectedKernel_conjugate]
  have he := finiteMean_equiv e (fun y : Tuples d l =>
    ((Fintype.card (Tuples d l):ℝ)*PairRouting.tupleProbability (palindromePerm d) (e.symm x) y)^
      (1+(1/1000:ℝ)))
  change finiteMean (fun y =>
    ((Fintype.card (Tuples d l):ℝ)*PairRouting.tupleProbability (palindromePerm d) (e.symm x) (e.symm y))^
      (1+(1/1000:ℝ))) ≤ _
  rw [←he]
  simpa only [palindromeRowMoment,Fintype.card_fin] using palindrome_row_moment_coarse d (e.symm x)

lemma tuples_card (d l : ℕ) : Fintype.card (Tuples d l) = (2^d).descFactorial l := by
  simp only [Tuples,Fintype.card_embedding_eq,Fintype.card_fin,card_positions]

lemma canonical_pointwise (d l : ℕ) (order : Equiv.Perm (Fin d)) (x y : Tuples d l) :
    ((reflectedKernel d l order false)^2000) x y ≤
      Real.exp ((2000*(1+heightDecay 1))*l)/((2^d).descFactorial l:ℝ) := by
  let : Nonempty (Tuples d l) := ⟨x⟩
  have hh := symmetric_kernel_smoothing (reflectedKernel d l order false)
    (reflected_nonneg d l order) (reflected_row d l order) (reflected_col d l order)
    (reflected_symmetric d l order) (p := 1+(1/1000:ℝ)) (A := l*(1+heightDecay 1))
    (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (by linarith [heightDecay_nonneg 1]))
    (reflected_moment d l order) 1000 density_exponent_numeric x y
  have he : 2*((l:ℝ)*(1+heightDecay 1))*(1000:ℝ) = (2000*(1+heightDecay 1))*l := by ring
  norm_num only [show 2*1000=2000 by norm_num,Nat.cast_ofNat] at hh
  simpa only [he,tuples_card] using hh

lemma both_pointwise (d l : ℕ) (order : Equiv.Perm (Fin d)) (orientation : Bool)
    (x y : Tuples d l) :
    ((reflectedKernel d l order orientation)^2001) x y ≤
      Real.exp ((2000*(1+heightDecay 1))*l)/((2^d).descFactorial l:ℝ) := by
  cases orientation
  · change ((reflectedKernel d l order false)^(2000+1)) x y ≤ _
    rw [pow_succ]
    exact bound_mul_right _ _ (reflected_nonneg d l order) (reflected_col d l order)
      (canonical_pointwise d l order) x y
  · let A := sweepKernel d l order
    change ((A*A.transpose)^(2000+1)) x y ≤ _
    rw [←sandwich_power]
    apply bound_mul_right _ _ (fun x y => sweepKernel_nonneg d l order y x)
      (sweepKernel_row d l order)
    exact bound_mul_left _ _ (sweepKernel_nonneg d l order) (sweepKernel_row d l order)
      (canonical_pointwise d l order)

lemma regular_trace_bound (d : ℕ) (order : Equiv.Perm (Fin d)) :
    regularAbsoluteEvenTrace d order 2001 ≤ Real.exp ((2000*(1+heightDecay 1))*(2:ℝ)^d) := by
  have hn : 0 < Fintype.card (Tuples d (2^d)) := by
    rw [tuples_card,Nat.descFactorial_self]
    exact Nat.factorial_pos _
  have hn' : (Fintype.card (Tuples d (2^d)):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  calc
    _ ≤ ∑ x : Tuples d (2^d), Real.exp ((2000*(1+heightDecay 1))*(2^d:ℕ)) /
        ((2^d).descFactorial (2^d):ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact both_pointwise d (2^d) order false x x
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←tuples_card]
      push_cast
      field_simp

theorem strong_smoothing : MainStatement := by
  refine ⟨2001,by norm_num,2000*(1+heightDecay 1),?_,regular_trace_bound⟩
  intro d l _ order orientation x y
  exact both_pointwise d l order orientation x y

end Thorp.StrongSmoothing

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht

lemma mem_tailDiagram (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ tailDiagram μ ↔ (i+1,j) ∈ μ := by
  rw [tailDiagram, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨hi,hj⟩
    rw [List.getElem_tail,YoungDiagram.get_rowLens] at hj
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  · intro h
    have hi : i+1 < μ.colLen 0 :=
      (YoungDiagram.mem_iff_lt_colLen.mp h).trans_le (μ.colLen_anti 0 j (Nat.zero_le _))
    have hi' : i < μ.rowLens.tail.length := by simp only [List.length_tail,YoungDiagram.length_rowLens]; omega
    refine ⟨hi', ?_⟩
    simpa only [List.getElem_tail,YoungDiagram.get_rowLens] using YoungDiagram.mem_iff_lt_rowLen.mp h

lemma tail_height (μ : YoungDiagram) : (tailDiagram μ).colLen 0 = μ.colLen 0 - 1 := by
  rw [←YoungDiagram.length_rowLens]
  exact (YoungDiagram.rowLens_length_ofRowLens (fun x hx => μ.pos_of_mem_rowLens x (List.mem_of_mem_tail hx))).trans
    (by simp only [List.length_tail,YoungDiagram.length_rowLens])

end Thorp.StrongTail

end ThorpNine.Tail

end OAI

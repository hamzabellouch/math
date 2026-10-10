import OAI.Probability.CubeShuffle.NetworkSpectral
import OAI.Probability.CubeShuffle.Physical
import OAI.RepresentationTheory.YoungSymmetry.ShapeBounds

namespace OAI

namespace CubeShuffle.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma medium_parameters (h : ℝ) (hh : 0<h) :
    ∃ L : ℕ, 0<L ∧ ∃ ε t : ℝ, 0<ε ∧ ε<1/2 ∧ 0≤t ∧
      t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000 ∧
      ∀ᶠ r : ℕ in atTop, ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
        ∀ e : Card (L+r) ↪ Card (L+r),
          modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r)) := by
  obtain ⟨L,hL,ε₀,hε₀,_,hM⟩ := modified_arbitrarily_small_rate (h/4000) (by positivity)
  obtain ⟨ε,hε,hεle,hεhalf,t,ht,hcount⟩ := exists_small_set_rate
    (h*(2:ℝ)^L/16000) ε₀ (by positivity) hε₀
  refine ⟨L,hL,ε,t,hε,hεhalf,ht,hcount,?_⟩
  filter_upwards [hM] with r hM
  intro E hE e
  exact hM E (hE.le.trans (mul_le_mul_of_nonneg_right hεle (by positivity))) e

end CubeShuffle.DimensionEstimates

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma dimension_pos (μ : YoungDiagram) : 0 < Module.finrank ℂ (space μ) := by
  have h := factorial_le_dimension_row_column μ
  by_contra hn
  have hz : Module.finrank ℂ (space μ)=0 := by omega
  rw [hz,zero_mul,zero_mul] at h
  exact (Nat.factorial_pos μ.card).not_ge h

lemma near_numerical_cutoff :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ (N j D : ℕ), 0 < j → X ≤ (N:ℝ)/j → N.choose j ≤ D * 2^j →
      ∃ k : ℕ, j ≤ k ∧ k ≤ N ∧ ∀ m : ℕ, D * k.choose j ≤ m * N.choose j →
        nearFraction * Real.log D ≤ Real.log m ∧
        densityConstant * (k:ℝ) * ((k:ℝ)/N)^(1/512:ℝ) ≤ Real.log m/4000 ∧
        (1/2:ℝ) * Real.log N ≤ Real.log D ∧ (j:ℝ) ≤ Real.log D := by
  obtain ⟨X,hX,h⟩ := exists_near_cutoff densityConstant densityConstant_pos.le
  refine ⟨X,hX,?_⟩
  intro N j D hj hx hd
  have hjN : j ≤ N := by
    have hjp : (0:ℝ) < j := by exact_mod_cast hj
    have hh : (j:ℝ) ≤ N := by
      have := (le_div_iff₀ hjp).mp (hX.trans hx)
      linarith
    exact_mod_cast hh
  have hc : 1 ≤ N.choose j := Nat.choose_pos hjN
  have hfoot : D * (chosenTuple N j).choose j ≤ (D * (chosenTuple N j).choose j) * N.choose j :=
    Nat.le_mul_of_pos_right _ hc
  have hh := h N j D _ hj hx hd hfoot
  refine ⟨chosenTuple N j,hh.1,hh.2.1,?_⟩
  intro m hm
  exact (h N j D m hj hx hd hm).2.2

lemma near_row_amplification (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
    {k : ℕ} (f : Fin k ↪ Card d) (hk : 0<k)
    (hm : 0<Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))) :
    ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
      Real.exp (densityConstant*(k:ℝ)*((k:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))^(-(1/1000:ℝ))+
      Real.sqrt ((Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))/
        (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)):ℝ)) := by
  let := relabelledUnitary_irreducible μ e
  let : NormedAddCommGroup (hilbertSpace μ) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ) := inferInstance
  have aux := @palindrome_irrep_amplification (hilbertSpace μ) _ _ _ d (Fin k) _ f
    (by simpa only [Fintype.card_fin] using hk) (relabelledUnitary μ e) inferInstance
    (relabelledUnitary_unitary μ e) hm
    (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))
    (Real.exp_pos _)
  simpa only [Fintype.card_fin] using aux

/-- Uniform near-row decay for the actual full-permutation palindrome.
The tuple size and fixed-space multiplicity are constructed, not assumed. -/
theorem near_row_spectral :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ),
      0 < μ.card-μ.rowLen 0 → X ≤ (μ.card:ℝ)/(μ.card-μ.rowLen 0:ℕ) →
      32768000 * Real.log 2 ≤ (1/2:ℝ) * Real.log μ.card →
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤ 
        Real.exp (-(nearFraction/8000) * Real.log (Module.finrank ℂ (space μ))) ∧
      (1/2:ℝ) * Real.log μ.card ≤ Real.log (Module.finrank ℂ (space μ)) ∧
      (μ.card-μ.rowLen 0:ℕ) ≤ Real.log (Module.finrank ℂ (space μ)) := by
  obtain ⟨X,hX,h⟩ := near_numerical_cutoff
  refine ⟨X,hX,?_⟩
  intro d μ e hj hx hlarge
  let j := μ.card-μ.rowLen 0
  let D := Module.finrank ℂ (space μ)
  have hcard : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  obtain ⟨k,hjk,hk,hnum⟩ := h μ.card j D hj hx (choose_tail_le_dimension μ)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin k) ≤ Fintype.card (Card d) by simpa only [Fintype.card_fin,card_positions,←hcard] using hk)
  let m := Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))
  have hfoot : D * k.choose j ≤ m * μ.card.choose j := by
    simpa only [Fintype.card_fin,finrank_hilbertSpace] using relabelled_tuple_dimension μ e f
  have hm : 0 < m := by
    have hc := Nat.choose_pos hjk
    have hd := dimension_pos μ
    by_contra hn
    have hz : m=0 := by omega
    rw [hz,zero_mul] at hfoot
    exact (Nat.mul_pos hd hc).not_ge hfoot
  obtain ⟨hlm,hden,hlog,hjlog⟩ := hnum m hfoot
  have ha := near_row_amplification d μ e f (hj.trans_le hjk) hm
  have hcardR : (μ.card:ℝ)=(2:ℝ)^d := by exact_mod_cast hcard
  rw [←hcardR] at ha
  have hl : 8000 * Real.log 2 ≤ Real.log m := by
    dsimp [nearFraction] at hlm
    linarith
  have hn := amplification_decay (m:ℝ) (densityConstant * k * ((k:ℝ)/μ.card)^(1/512:ℝ))
    (by exact_mod_cast hm) hden hl
  refine ⟨ha.trans (hn.trans ?_),hlog,hjlog⟩
  apply Real.exp_le_exp.mpr
  dsimp [D] at hlm
  linarith

end CubeShuffle.Specht

namespace CubeShuffle.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem medium_exception_decay (L r : ℕ) (h ε t : ℝ) (ht : 0≤t)
    (hcount : t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hd : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ V))
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V))
    (hM : ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
      ∀ e : Card (L+r) ↪ Card (L+r),
        modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r))) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖≤
      Real.exp (Real.log (blockGap L)*ε*(2:ℝ)^r)+Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
  have hmE (E : Finset (Card r)) (hE : E.card<⌈ε*(2:ℝ)^r⌉₊) :
      ‖sampleOperator ρ (modifiedPerm L r E)‖≤Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
    apply (full_modified_decay L r E ρ hρ hm ((h/4000)*(2:ℝ)^(L+r))
      (hM E (Nat.lt_ceil.mp hE)) (by linarith) hl).trans
    apply Real.exp_le_exp.mpr
    linarith
  have hs : (∑ E : Finset (Card r), if E.card<⌈ε*(2:ℝ)^r⌉₊ then
      ‖sampleOperator ρ (modifiedPerm L r E)‖ else 0) ≤
      Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
    calc
      _ ≤ (∑ E : Finset (Card r), if E.card<⌈ε*(2:ℝ)^r⌉₊ then (1:ℝ) else 0)*
          Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro E _
        split_ifs with hE
        · simpa only [one_mul] using hmE E hE
        · simp
      _ ≤ Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*(2:ℝ)^r)*
          Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        simpa only [card_positions,Nat.cast_pow,Nat.cast_ofNat] using
          small_sets_ceil_bound (ι := Card r) ε t ht
      _ ≤ _ := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hcount (by positivity : (0:ℝ)≤(2:ℝ)^r)
        rw [pow_add]
        nlinarith
  apply (palindrome_exception_cards r L ρ hρ ⌈ε*(2:ℝ)^r⌉₊).trans
  apply add_le_add _ hs
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    geometric_ceil_bound (blockGap L) ε (blockGap_pos L) (blockGap_lt_one L) (2^r)

end CubeShuffle.UnitaryFinite

namespace CubeShuffle
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

end CubeShuffle
namespace CubeShuffle.Specht
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

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical
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

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

/-- Every exponentially large irreducible has the same absolute power decay.
Both the high-dimensional FAC.1 and medium-dimensional FAC.2 regimes are used. -/
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

end CubeShuffle.Specht

namespace CubeShuffle.Specht
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

/-- The nontrivial full-deck spectral regimes, with one absolute exponent.
The two dimension alternatives are precisely those needed by the shape sum. -/
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

end CubeShuffle.Specht

end OAI

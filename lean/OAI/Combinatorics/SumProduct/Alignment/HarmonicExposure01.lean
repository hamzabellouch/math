import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughFace01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end
 

section
 
noncomputable section
namespace RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 

theorem source_face_decay (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B K : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (S : ℕ → Fin m → ℝ) (Z H : ℕ→ℝ)
    (r : ℕ → Fin m → ℤ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(1+∑ j,S n j)^a) atTop atTop)
    (hH : ∀ n,0≤H n) (hHZ : Tendsto (fun n=>H n/Z n) atTop (𝓝 0))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hr : ∀ n j,(r n j).natAbs.Coprime (primorial (w n)))
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes (S n) (r n) (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes (S n) (r n) (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      ((exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n)).card:ℝ)/
        ((productTimes (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  let B' : NNReal := B*(K+1)
  have hB' : 0<B' := mul_pos hB (by positivity)
  have hBB : B≤B' := by
    dsimp [B']
    calc
      B=B*1 := by ring
      _≤B*(K+1) := mul_le_mul_of_nonneg_left (by nlinarith [K.2]) B.2
  have hBK : B*K≤B' := by
    dsimp [B']
    rw [mul_add,mul_one]
    exact le_add_of_nonneg_right B.2
  have hz : Tendsto Z atTop atTop := by
    have h := domination_smaller (S:=fun _=>1) (T:=fun n=>totalScale (S n))
      (by filter_upwards [] with n; norm_num) (totalScale_pos_eventually S hS) hZ
    simpa using h 1 zero_lt_one
  have herr : Tendsto (fun n=>(8*(B:ℝ)*(v:ℝ)/c₀)*(H n/Z n)) atTop (𝓝 0) := by
    simpa using hHZ.const_mul (8*(B:ℝ)*(v:ℝ)/c₀)
  intro ε hε
  have hp := source_product_decay c Γ hsk hΓ htop m v D d hd c₀ C₀ B' (η/4)
    hc₀ hC₀ hB' (by positivity) w M S Z r L hw hS hZ hM hMs hL hsm hWL hr hSL ε hε
  filter_upwards [hp,hz.eventually (eventually_ge_atTop (4*(d:ℝ)/c₀)),
    herr.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/4))] with n hpn hzn hen
  intro A P hP σ hσ h hh hid
  have hW : 4*(d:ℝ)≤c₀*Z n := by
    have ht := (div_le_iff₀ hc₀).mp hzn
    nlinarith
  have hsub : exceptionalFace Γ m v c₀ C₀ B η (Z n) d (M n) A P σ (S n) (r n) (L n) ⊆
      exceptionalProduct Γ m v c₀ C₀ B' (η/4) (Z n) d (M n) A P (S n) (r n) (L n) := by
    intro t ht
    obtain ⟨ht,hbad⟩ := Finset.mem_filter.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨ht,?_⟩
    by_contra hgood
    obtain ⟨lo,hi,res,test,hside,hbox,hLip,hnorm,hlarge⟩ := hbad
    have hcompare (F : (G⧸Γ) → ℂ) (hFL : LipschitzWith B' F) (hFn : ∀ y,‖F y‖≤B') :
        ‖mean (physicalResidueBox lo hi res d)
          (fun x=>F (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))-
        mean (nestedBox lo hi res A d (M n) (∏ j,t j))
          (fun x=>F (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))‖<η/4 := by
      apply lt_of_not_ge
      intro hh
      exact hgood ⟨lo,hi,res,F,hside,hbox,hFL,hFn,hh⟩
    have hplain := hcompare test (hLip.weaken hBB)
      (fun y=>(hnorm y).trans (by exact_mod_cast hBB))
    have hface := hcompare (fun y=>test (σ y)) ((hLip.comp hσ).weaken hBK)
      (fun y=>(hnorm (σ y)).trans (by exact_mod_cast hBB))
    let f : (Fin v → ℤ) → ℂ := fun x=>test
      (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))
    have hshift := residueMean_translation lo hi res (h t) d hd (B:ℝ) (c₀*Z n) (H n)
      hB hW hside (hH n) (hh t ht) f (fun x=>hnorm _)
    have he : (fun x : Fin v → ℤ=>test
        (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))=
        fun x=>f (x+h t) := by
      funext x
      rw [hid t ht x]
      rfl
    have hsmall : ‖mean (physicalResidueBox lo hi res d) (fun x=>f (x+h t))-
        mean (physicalResidueBox lo hi res d) f‖<η/4 := by
      apply hshift.trans_lt
      convert hen using 1
      ring
    rw [← he] at hsmall
    let X := mean (nestedBox lo hi res A d (M n) (∏ j,t j))
      (fun x=>test (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))
    let Y := mean (physicalResidueBox lo hi res d)
      (fun x=>test (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))
    let U := mean (physicalResidueBox lo hi res d) f
    let V := mean (nestedBox lo hi res A d (M n) (∏ j,t j)) f
    have htri : ‖X-V‖≤‖X-Y‖+‖Y-U‖+‖U-V‖ := by
      calc
        _≤‖X-U‖+‖U-V‖ := norm_sub_le_norm_sub_add_norm_sub X U V
        _≤_ := add_le_add (norm_sub_le_norm_sub_add_norm_sub X Y U) (le_refl ‖U-V‖)
    change η≤‖X-V‖ at hlarge
    change ‖U-V‖<η/4 at hplain
    change ‖Y-X‖<η/4 at hface
    rw [norm_sub_rev] at hface
    change ‖Y-U‖<η/4 at hsmall
    linarith
  exact (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
    (Nat.cast_nonneg _)).trans_lt (hpn A P hP)

end RoughFaceShift
end
end
 

section
 
noncomputable section
namespace HarmonicExposure
open RoughSamplingWeights RoughSourceExceptional RoughProductRemoval
open scoped BigOperators

 
def pivotMass (Q Δ τ : ℝ) (a M : ℤ) : ℝ :=
  ∑ k∈indices (Q/τ) ((Q+Δ)/τ) a M, ((a:ℝ)+(M:ℝ)*(k:ℝ))⁻¹

def exposedWeight {m : ℕ} (Q Δ : ℝ) (a M : ℤ) (t : Fin m → ℤ) : ℝ :=
  (∏ j,(t j:ℝ)⁻¹) * pivotMass Q Δ (∏ j,(t j:ℝ)) a M

lemma pivot_bounds (Q Δ τ : ℝ) (a M : ℤ) (hM : 0<M) (hQ : 0<Q)
    (hΔ : 0<Δ) (hτ : 0<τ) (hΔQ : Δ≤Q) (hsize : 4*(M:ℝ)*τ≤Δ) :
    Δ/(4*(M:ℝ)*Q)≤pivotMass Q Δ τ a M ∧
      pivotMass Q Δ τ a M≤8*(Δ/(4*(M:ℝ)*Q)) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  let T := indices (Q/τ) ((Q+Δ)/τ) a M
  let ν := Δ/((M:ℝ)*τ)
  have hν : 4≤ν := (le_div_iff₀ (mul_pos hMr hτ)).mpr (by nlinarith)
  have hc := count_error (Q/τ) ((Q+Δ)/τ) a M hMr
    (div_le_div_of_nonneg_right (by linarith) hτ.le)
  have he : ((Q+Δ)/τ-Q/τ)/(M:ℝ)=ν := by dsimp [ν]; ring
  rw [he] at hc
  change |(T.card:ℝ)-ν|≤2 at hc
  have hNl : ν/2≤(T.card:ℝ) := by have := (abs_le.mp hc).1; linarith
  have hNu : (T.card:ℝ)≤2*ν := by have := (abs_le.mp hc).2; linarith
  have hpoint : ∀ k∈T, τ/(Q+Δ)≤((a:ℝ)+(M:ℝ)*(k:ℝ))⁻¹ ∧
      ((a:ℝ)+(M:ℝ)*(k:ℝ))⁻¹≤τ/Q := by
    intro k hk
    have hb := (mem_indices (Q/τ) ((Q+Δ)/τ) a M hMr k).mp hk
    have hp : 0<(a:ℝ)+(M:ℝ)*(k:ℝ) := (div_pos hQ hτ).trans_le hb.1
    constructor
    · simpa only [one_div,inv_div] using one_div_le_one_div_of_le hp hb.2.le
    · simpa only [one_div,inv_div] using one_div_le_one_div_of_le (div_pos hQ hτ) hb.1
  have hlo : (ν/2)*(τ/(Q+Δ))≤pivotMass Q Δ τ a M := by
    calc
      _≤(T.card:ℝ)*(τ/(Q+Δ)) := mul_le_mul_of_nonneg_right hNl (by positivity)
      _=∑ _k∈T,τ/(Q+Δ) := by simp
      _≤_ := Finset.sum_le_sum (fun k hk=>(hpoint k hk).1)
  have hhi : pivotMass Q Δ τ a M≤(2*ν)*(τ/Q) := by
    calc
      _≤∑ _k∈T,τ/Q := Finset.sum_le_sum (fun k hk=>(hpoint k hk).2)
      _=(T.card:ℝ)*(τ/Q) := by simp
      _≤_ := mul_le_mul_of_nonneg_right hNu (by positivity)
  constructor
  · apply LE.le.trans ?_ hlo
    have hid : (ν/2)*(τ/(Q+Δ))=Δ/(2*(M:ℝ)*(Q+Δ)) := by
      dsimp [ν]
      field_simp
    rw [hid]
    apply div_le_div_of_nonneg_left hΔ.le (by positivity)
    nlinarith
  · apply hhi.trans_eq
    dsimp [ν]
    field_simp
    ring

lemma exposed_weight_bounds (m : ℕ) (S : Fin m → ℝ) (r : Fin m → ℤ) (L a M : ℤ)
    (Q Δ : ℝ) (hS : ∀ j,0<S j) (hL : 0<L) (hM : 0<M) (hQ : 0<Q)
    (hΔ : 0<Δ) (hΔQ : Δ≤Q) (hsize : 4*(M:ℝ)*(2^m*∏ j,S j)≤Δ)
    (t : Fin m → ℤ) (ht : t∈productTimes S r L) :
    (Δ/(4*(M:ℝ)*Q))/(2^m*∏ j,S j)≤exposedWeight Q Δ a M t ∧
      exposedWeight Q Δ a M t≤(8*2^m)*((Δ/(4*(M:ℝ)*Q))/(2^m*∏ j,S j)) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hb (j : Fin m) : S j≤(t j:ℝ) ∧ (t j:ℝ)<2*S j := by
    have hh := (Fintype.mem_piFinset.mp ht) j
    have hi := (mem_times (S j) (r j) L (t j) hL).mp hh
    exact ⟨hi.1,hi.2.1⟩
  have htp : ∀ j,0<(t j:ℝ) := fun j=>(hS j).trans_le (hb j).1
  have hsp : (0:ℝ)<∏ j,S j := Finset.prod_pos (fun j _=>hS j)
  have hτ : (0:ℝ)<∏ j,(t j:ℝ) := Finset.prod_pos (fun j _=>htp j)
  have hlo : (∏ j,S j)≤∏ j,(t j:ℝ) := Finset.prod_le_prod₀
    (fun j _=>(hS j).le) (fun j _=>(hb j).1)
  have hhi : (∏ j,(t j:ℝ))≤2^m*∏ j,S j := by
    calc
      _≤∏ j,2*S j := Finset.prod_le_prod₀ (fun j _=>(htp j).le) (fun j _=>(hb j).2.le)
      _=_ := by rw [Finset.prod_mul_distrib]; simp
  have hsz : 4*(M:ℝ)*(∏ j,(t j:ℝ))≤Δ :=
    (mul_le_mul_of_nonneg_left hhi (by positivity)).trans hsize
  have hmass := pivot_bounds Q Δ (∏ j,(t j:ℝ)) a M hM hQ hΔ hτ hΔQ hsz
  have he : exposedWeight Q Δ a M t=pivotMass Q Δ (∏ j,(t j:ℝ)) a M/(∏ j,(t j:ℝ)) := by
    dsimp [exposedWeight]
    rw [Finset.prod_inv_distrib,div_eq_mul_inv,mul_comm]
  rw [he]
  constructor
  · calc
      _≤(Δ/(4*(M:ℝ)*Q))/(∏ j,(t j:ℝ)) := div_le_div_of_nonneg_left (by positivity) hτ hhi
      _≤_ := div_le_div_of_nonneg_right hmass.1 hτ.le
  · calc
      _≤(8*(Δ/(4*(M:ℝ)*Q)))/(∏ j,(t j:ℝ)) := div_le_div_of_nonneg_right hmass.2 hτ.le
      _≤(8*(Δ/(4*(M:ℝ)*Q)))/(∏ j,S j) := div_le_div_of_nonneg_left (by positivity) hsp hlo
      _=_ := by field_simp

lemma weighted_fraction_bound {α : Type*} (T E : Finset α) (hT : T.Nonempty)
    (hE : E⊆T) (f : α → ℝ) (A K : ℝ) (hA : 0<A) (hK : 0≤K)
    (hf : ∀ t∈T,A≤f t ∧ f t≤K*A) :
    (∑ t∈E,f t)/(∑ t∈T,f t)≤K*((E.card:ℝ)/(T.card:ℝ)) := by
  have hcard : (0:ℝ)<T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hlo : (T.card:ℝ)*A≤∑ t∈T,f t := by
    calc
      _=∑ _t∈T,A := by simp
      _≤_ := Finset.sum_le_sum (fun t ht=>(hf t ht).1)
  have htotal : (0:ℝ)<∑ t∈T,f t := (mul_pos hcard hA).trans_le hlo
  have hhi : (∑ t∈E,f t)≤(E.card:ℝ)*(K*A) := by
    calc
      _≤∑ _t∈E,K*A := Finset.sum_le_sum (fun t ht=>(hf t (hE ht)).2)
      _=_ := by simp
  apply (div_le_iff₀ htotal).mpr
  calc
    _≤(E.card:ℝ)*(K*A) := hhi
    _=(K*((E.card:ℝ)/(T.card:ℝ)))*((T.card:ℝ)*A) := by field_simp
    _≤_ := mul_le_mul_of_nonneg_left hlo (by positivity)

theorem conditional_fraction_le (m : ℕ) (S : Fin m → ℝ) (r : Fin m → ℤ) (L a M : ℤ)
    (Q Δ : ℝ) (hS : ∀ j,0<S j) (hL : 0<L) (hM : 0<M) (hQ : 0<Q)
    (hΔ : 0<Δ) (hΔQ : Δ≤Q) (hsize : 4*(M:ℝ)*(2^m*∏ j,S j)≤Δ)
    (hT : (productTimes S r L).Nonempty) (E : Finset (Fin m → ℤ))
    (hE : E⊆productTimes S r L) :
    (∑ t∈E,exposedWeight Q Δ a M t)/(∑ t∈productTimes S r L,exposedWeight Q Δ a M t) ≤
      (8*2^m)*((E.card:ℝ)/((productTimes S r L).card:ℝ)) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hsp : (0:ℝ)<∏ j,S j := Finset.prod_pos (fun j _=>hS j)
  apply weighted_fraction_bound _ E hT hE _ ((Δ/(4*(M:ℝ)*Q))/(2^m*∏ j,S j)) (8*2^m)
    (by positivity) (by positivity)
  exact exposed_weight_bounds m S r L a M Q Δ hS hL hM hQ hΔ hΔQ hsize

end HarmonicExposure

end
end

end OAI

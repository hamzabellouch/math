import OAI.Combinatorics.HoneycombChords.JetCompression

namespace OAI

/-!
# Oblique characteristic product estimates

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma positive_ratio_reversal {S Q l:ℝ} (hS:0<S) (hQ:0<Q) (hl:0<l)
    (h1:l*S≤Q) (h2:Q≤S) : S⁻¹≤Q⁻¹ ∧ Q⁻¹≤l⁻¹*S⁻¹ := by
  constructor
  · exact (inv_le_inv₀ hS hQ).mpr h2
  · have h:Q⁻¹≤(l*S)⁻¹:=(inv_le_inv₀ hQ (mul_pos hl hS)).mpr h1
    simpa only [_root_.mul_inv_rev,mul_comm] using h
theorem pole_knot_expansion_comparison (N : ℕ) {s t y z : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (hz : 0<z) (hzy : z≤y) :
    let M:=twoKnotLabels N
    let F:=interiorKnotLabels N s
    let G:=interiorKnotLabels N t
    let S:=(jetPencil (n:=2*N) (poleAdjustedDensity z) M M (-(y^2))).det/
      (jetPencil (n:=2*N) (poleAdjustedDensity z) M M (-(z^2))).det
    let Q:=(jetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(y^2))).det/
      (jetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(z^2))).det
    S ≤ Q ∧ Q ≤ (y^2/z^2)*S := by
  dsimp only
  have hy : 0<y := hz.trans_le hzy
  let A:=reorderedKnotPencil N s t z 0
  let B:=reorderedKnotGram N s t z
  have hA : (A.submatrix Fin.castSucc Fin.castSucc).PosDef := by
    rw [show A=reorderedKnotPencil N s t z 0 from rfl,reorderedKnotPencil_corner N hs hsL ht htL]
    exact pole_jetPencil_zero_posDef _ hz (fun _ _ hij=>twoKnot_monotone N hij) (fun i=>twoKnot_nonneg N i) (fun i=>twoKnot_le N i)
  have hB : (B.submatrix Fin.castSucc Fin.castSucc).PosDef := by
    rw [show B=reorderedKnotGram N s t z from rfl,reorderedKnotGram_corner N hs hsL ht htL]
    exact pole_jetGram_posDef _ hz (fun _ _ hij=>twoKnot_monotone N hij) (fun i=>twoKnot_nonneg N i) (fun i=>twoKnot_le N i)
  have h0 : 0<A.det := reorderedKnotPencil_det_pos_nonpos N hs hsL ht htL hz le_rfl
  have h1 : 0<B.det := reorderedKnotGram_det_pos N hs hsL ht htL hz
  have hres (r : ℝ) (x : Fin (2*N) → ℝ) (hx : x≠0)
      (hk : x ᵥ* ((A-r • B).submatrix Fin.castSucc Fin.castSucc)=0) :
      0 ≤ lastPairing (A-r • B) x*lastPairing (A-r • B).transpose x := by
    dsimp only [A,B] at hk ⊢
    rw [←reorderedKnotPencil_affine N hs hsL ht htL hz r] at hk ⊢
    rw [reorderedKnotPencil_corner N hs hsL ht htL] at hk
    rw [reorderedKnotPencil_transpose]
    simp only [lastPairing,reorderedKnotPencil_vecMul_last N hs hsL ht htL,
      reorderedKnotPencil_vecMul_last N ht htL hs hsL]
    exact (knotPairing_product_pos N hz x hx r hk ht htL hs hsL).le
  have h:=fin_pencil_ratio A B hA hB h0 h1 hres (sq_pos_of_pos hz) (by nlinarith : z^2 ≤ y^2)
  have heq (u : ℝ) : A+u • B=reorderedKnotPencil N s t z (-u) := by
    rw [reorderedKnotPencil_affine N hs hsL ht htL hz]
    simp only [neg_smul,sub_neg_eq_add]
    rfl
  rw [heq (y^2),heq (z^2)] at h
  simp only [reorderedKnotPencil_corner N hs hsL ht htL] at h
  simp only [reorderedKnotPencil,Matrix.det_submatrix_equiv_self] at h
  let S:=(jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(z^2))).det /
    (jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(y^2))).det
  let Q:=(jetPencil (n:=2*N+1) (poleAdjustedDensity z) (interiorKnotLabels N s) (interiorKnotLabels N t) (-(z^2))).det /
    (jetPencil (n:=2*N+1) (poleAdjustedDensity z) (interiorKnotLabels N s) (interiorKnotLabels N t) (-(y^2))).det
  have hSdet (u:ℝ):0<(jetPencil (n:=2*N) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(u^2))).det:=by
    exact pole_jetPencil_det_pos_nonpos _ _ hz (neg_nonpos.mpr (sq_nonneg u))
      (fun _ _ hij=>twoKnot_monotone N hij) (fun _ _ hij=>twoKnot_monotone N hij)
      (fun i=>twoKnot_nonneg N i) (fun i=>twoKnot_nonneg N i)
      (fun i=>(twoKnot_le N i).trans (by nlinarith [sq_nonneg angle])) (fun i=>twoKnot_le N i)
  have hQdet (u:ℝ):0<(jetPencil (n:=2*N+1) (poleAdjustedDensity z) (interiorKnotLabels N s) (interiorKnotLabels N t) (-(u^2))).det:=by
    have hh:=reorderedKnotPencil_det_pos_nonpos N hs hsL ht htL hz (neg_nonpos.mpr (sq_nonneg u))
    simpa only [reorderedKnotPencil,Matrix.det_submatrix_equiv_self] using hh
  have hS:0<S:=div_pos (hSdet z) (hSdet y)
  have hQ:0<Q:=div_pos (hQdet z) (hQdet y)
  have hInv:=positive_ratio_reversal hS hQ (by positivity : 0<z^2/y^2) h.1 h.2
  simpa only [S,Q,inv_div,_root_.mul_inv_rev,div_inv_eq_mul,mul_comm] using hInv
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Filter Topology Real
/-- The fixed positive-parameter characteristic product for the literal
symmetric complete-jet space and the original strip density. -/
theorem twoJet_characteristic_bounds {y z:ℝ} (hy:0<y) (hyz:y<z) :
    ∃ a A:ℝ,0<a ∧ 0<A ∧ ∀ᶠ N:ℕ in atTop,
      a*((N:ℝ)+1)^(3*(y-z)/8)≤
        (familyGram (fun p=>characteristicRatio y z p*stripDensity p) (twoJetFamily N) (twoJetFamily N)).det /
          (familyGram stripDensity (twoJetFamily N) (twoJetFamily N)).det ∧
      (familyGram (fun p=>characteristicRatio y z p*stripDensity p) (twoJetFamily N) (twoJetFamily N)).det /
          (familyGram stripDensity (twoJetFamily N) (twoJetFamily N)).det≤A*((N:ℝ)+1)^(3*(y-z)/8) := by
  obtain ⟨C,hC,hcomp⟩:=twoJetPolynomialCompression
  obtain ⟨a,A,ha,hA,hpoly⟩:=strip_polynomial_characteristic_product_bounds hy (hy.trans hyz)
  obtain ⟨N₀,hN₀⟩:=eventually_atTop.mp hpoly
  let s:ℝ:=3*(y-z)/8
  have hs:s≤0:=by dsimp [s];linarith
  have hc0:0<(C:ℝ)+1:=by positivity
  refine ⟨a*((C:ℝ)+1)^s/4,A,by positivity,hA,?_⟩
  filter_upwards [hcomp y z hy hyz,eventually_ge_atTop N₀] with N hn hN
  have hle:N≤C*N:=by nlinarith
  have hCN:=hN₀ (C*N) (hN.trans hle)
  have hNN:=hN₀ N hN
  have hscale:((C:ℝ)+1)^s*((N:ℝ)+1)^s≤((C*N:ℕ)+1:ℝ)^s:=by
    rw [←Real.mul_rpow hc0.le (by positivity)]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hs
    simp only [Nat.cast_mul]
    nlinarith [Nat.cast_nonneg (α:=ℝ) C,Nat.cast_nonneg (α:=ℝ) N]
  constructor
  · calc
      (a*((C:ℝ)+1)^s/4)*((N:ℝ)+1)^s=(a/4)*(((C:ℝ)+1)^s*((N:ℝ)+1)^s):=by ring
      _≤(a/4)*((C*N:ℕ)+1:ℝ)^s:=mul_le_mul_of_nonneg_left hscale (by positivity)
      _≤(monomialGram (C*N) (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram (C*N) stripDensity).det/4:=by
        dsimp only [s]
        linarith [hCN.1]
      _≤_:=hn.1
  · exact hn.2.trans hNN.2
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology
lemma polePencil_characteristic_gram {n:ℕ} (b c:ℕ→ℝ) (y z:ℝ) :
    jetPencil (n:=n) (poleAdjustedDensity z) b c (-(y^2))=
      jetGram (fun p=>characteristicRatio y z p*stripDensity p) b c := by
  ext i j
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [jetPencil,jetGram,poleAdjustedDensity,characteristicRatio]
  ring
lemma polePencil_original_gram {n:ℕ} (b c:ℕ→ℝ) {z:ℝ} (hz:0<z) :
    jetPencil (n:=n) (poleAdjustedDensity z) b c (-(z^2))=jetGram stripDensity b c := by
  rw [polePencil_characteristic_gram]
  congr 1
  funext p
  have hd:(p^2+z^2)≠0:=by positivity
  simp only [characteristicRatio,div_self hd,one_mul]
/-- A uniform determinant product bound for the first nonsymmetric family. -/
theorem first_oblique_characteristic_product_bounds {y z:ℝ} (hy:0<y) (hyz:y<z) :
    ∃ a A:ℝ,0<a ∧ 0<A ∧ ∀ᶠ N:ℕ in atTop,∀ s t:ℝ,0<s→s<angle→0<t→t<angle→
      a*((N:ℝ)+1)^(3*(y-z)/8)≤
        (jetGram (n:=2*N+1) (fun p=>characteristicRatio y z p*stripDensity p)
          (interiorKnotLabels N s) (interiorKnotLabels N t)).det /
        (jetGram (n:=2*N+1) stripDensity (interiorKnotLabels N s) (interiorKnotLabels N t)).det ∧
      (jetGram (n:=2*N+1) (fun p=>characteristicRatio y z p*stripDensity p)
          (interiorKnotLabels N s) (interiorKnotLabels N t)).det /
        (jetGram (n:=2*N+1) stripDensity (interiorKnotLabels N s) (interiorKnotLabels N t)).det≤
        A*((N:ℝ)+1)^(3*(y-z)/8) := by
  obtain ⟨a,A,ha,hA,hbounds⟩:=twoJet_characteristic_bounds hy hyz
  have hz:=hy.trans hyz
  have hl:0<y^2/z^2:=by positivity
  refine ⟨(y^2/z^2)*a,A,by positivity,hA,?_⟩
  filter_upwards [hbounds] with N hN
  intro s t hs hsL ht htL
  have h:=pole_knot_characteristic_comparison N hs hsL ht htL hy hyz
  dsimp only at h
  simp only [polePencil_original_gram _ _ hz] at h
  simp only [polePencil_characteristic_gram _ _ y z] at h
  change a*((N:ℝ)+1)^(3*(y-z)/8)≤
      (jetGram (n:=2*N) (fun p=>characteristicRatio y z p*stripDensity p) (twoKnotLabels N) (twoKnotLabels N)).det/
      (jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N)).det ∧ _ at hN
  constructor
  · calc
      ((y^2/z^2)*a)*((N:ℝ)+1)^(3*(y-z)/8)=(y^2/z^2)*(a*((N:ℝ)+1)^(3*(y-z)/8)):=by ring
      _≤_:=mul_le_mul_of_nonneg_left hN.1 hl.le
      _≤_:=h.1
  · exact h.2.trans hN.2
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology
lemma polynomial_characteristic_le_one_square (n:ℕ) {y z:ℝ} (hy:0<y) (hz:0<z) :
    (monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram n stripDensity).det ≤
    1+(monomialGram n (fun p=>characteristicRatio y z p^2*stripDensity p)).det/(monomialGram n stripDensity).det := by
  have hB:0<(monomialGram n stripDensity).det:=
    (monomialGram_posDef n _ (fun _ hp=>stripDensity_pos hp) stripDensity_moments).det_pos
  have hcs:=monomialGram_tilt_square n stripDensity (characteristicRatio y z)
    (fun _ hp=>stripDensity_pos hp) stripDensity_moments
    (by simpa only [pow_one] using characteristic_tilt_moments hy hz 1)
    (characteristic_tilt_moments hy hz 2)
  have hsq:
      ((monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram n stripDensity).det)^2 ≤
      (monomialGram n (fun p=>characteristicRatio y z p^2*stripDensity p)).det/(monomialGram n stripDensity).det:=by
    rw [div_pow]
    have hh:=div_le_div_of_nonneg_right hcs (sq_nonneg (monomialGram n stripDensity).det)
    exact hh.trans_eq (by field_simp [hB.ne'])
  nlinarith [sq_nonneg ((monomialGram n (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram n stripDensity).det-1)]
/-- A uniform subexponential characteristic bound for the first nonsymmetric family at the moving scale `y² = 2z² = 2N^(3/2)`. -/
theorem first_oblique_growing_product_bound :
    ∃ D:ℕ,0<D ∧ ∃ c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠ N:ℕ in atTop,
      ∀ y z:ℝ,1≤z→z≤y→y^2≤2*z^2→1/2≤c*y/Real.pi→
      ∀ s t:ℝ,0<s→s<angle→0<t→t<angle→
      (jetGram (n:=2*N+1) (fun p=>characteristicRatio y z p*stripDensity p)
        (interiorKnotLabels N s) (interiorKnotLabels N t)).det /
      (jetGram (n:=2*N+1) stripDensity (interiorKnotLabels N s) (interiorKnotLabels N t)).det ≤
      8*(1+C*z^4*((D*N:ℕ)+1:ℝ)^3*(4*((D*N:ℕ)+1:ℝ))^(2*c*y/Real.pi+1)) := by
  obtain ⟨D,hD,htwo⟩:=twoJet_polynomial_expansion_uniform
  obtain ⟨c,C,hc,hC,hpoly⟩:=strip_polynomial_square_product_uniform
  refine ⟨D,hD,c,C,hc,hC,?_⟩
  filter_upwards [htwo] with N hN
  intro y z hz hzy hyz hs s t hss hsL ht htL
  have hz0:0<z:=by linarith
  have hy0:=hz0.trans_le hzy
  have h:=pole_knot_expansion_comparison N hss hsL ht htL hz0 hzy
  dsimp only at h
  simp only [polePencil_original_gram _ _ hz0] at h
  simp only [polePencil_characteristic_gram _ _ y z] at h
  have hj:=hN y z hz0 hzy hyz
  have he_tilt:familyGram (fun p=>characteristicRatio y z p*stripDensity p) (twoJetFamily N) (twoJetFamily N)=
      jetGram (n:=2*N) (fun p=>characteristicRatio y z p*stripDensity p) (twoKnotLabels N) (twoKnotLabels N):=rfl
  have he_base:familyGram stripDensity (twoJetFamily N) (twoJetFamily N)=
      jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N):=rfl
  rw [he_tilt,he_base] at hj
  have hJpos:0≤(jetGram (n:=2*N) (fun p=>characteristicRatio y z p*stripDensity p) (twoKnotLabels N) (twoKnotLabels N)).det /
      (jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N)).det:=
    (div_pos (twoJetFamily_tilt_posDef N hy0 hz0).det_pos (twoJetFamily_posDef N).det_pos).le
  have hratio:y^2/z^2≤2:=(div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have ho:=(polynomial_characteristic_le_one_square (D*N) hy0 hz0).trans
    (show 1 + _ ≤ 1 + C*z^4*((D*N:ℕ)+1:ℝ)^3*(4*((D*N:ℕ)+1:ℝ))^(2*c*y/Real.pi+1) by
      linarith [hpoly y z hz hs (D*N)])
  have htop:=h.2.trans (mul_le_mul_of_nonneg_right hratio hJpos)
  have htop':=htop.trans (mul_le_mul_of_nonneg_left hj (by norm_num : (0:ℝ)≤2))
  have hfinal:=mul_le_mul_of_nonneg_left ho (by norm_num : (0:ℝ)≤8)
  calc
    _≤2*(4*((monomialGram (D*N) (fun p=>characteristicRatio y z p*stripDensity p)).det /
        (monomialGram (D*N) stripDensity).det)):=htop'
    _=8*((monomialGram (D*N) (fun p=>characteristicRatio y z p*stripDensity p)).det /
        (monomialGram (D*N) stripDensity).det):=by ring
    _≤_:=hfinal
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def zeroJetMatrix (n:ℕ) (b:ℕ→ℝ) : Matrix (Fin n) (Fin (n+1)) ℝ :=
  fun i=>Fin.cons (-cosineKernelJet (nodalOrder b (i.val+1)) 0 (b (i.val+1)) 0) (Pi.single i 1)
lemma zeroJetMatrix_representation (n:ℕ) (b:ℕ→ℝ) (hb:b 0=0) (i:Fin n) :
    finiteFamilyCombination (fun j:Fin (n+1)=>cosineKernelJet (nodalOrder b j) 0 (b j)) (zeroJetMatrix n b i)=zeroJet b i := by
  funext x
  dsimp only [finiteFamilyCombination,zeroJetMatrix]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,Fin.val_zero,Fin.val_succ,jet_first_constant b hb,mul_one]
  simp [Pi.single_apply,zeroJet,sub_eq_add_neg,add_comm]
lemma zeroJetMatrix_transpose_injective (n:ℕ) (b:ℕ→ℝ) :
    Function.Injective (zeroJetMatrix n b)ᵀ.mulVec := by
  intro u v huv
  funext i
  have h:=congrFun huv i.succ
  simpa [Matrix.mulVec,dotProduct,zeroJetMatrix,Pi.single_apply] using h
lemma zeroJet_gram_compression (n:ℕ) (b:ℕ→ℝ) (hb:b 0=0) (w:ℝ→ℝ)
    (hi:∀ i j:Fin (n+1),IntegrableOn (fun p=>
      cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*cosineKernelJet (nodalOrder b j) 0 (b j) (p^2)*w p) (Set.Ioi 0)) :
    familyGram w (fun i:Fin n=>zeroJet b i) (fun i:Fin n=>zeroJet b i)=
      zeroJetMatrix n b*jetGram (n:=n+1) w b b*(zeroJetMatrix n b)ᵀ := by
  have h:=familyGram_congruence w (fun i:Fin (n+1)=>cosineKernelJet (nodalOrder b i) 0 (b i)) hi (zeroJetMatrix n b)
  simp only [zeroJetMatrix_representation n b hb] at h
  have hJ:familyGram w (fun i:Fin (n+1)=>cosineKernelJet (nodalOrder b i) 0 (b i))
      (fun i:Fin (n+1)=>cosineKernelJet (nodalOrder b i) 0 (b i))=jetGram (n:=n+1) w b b:=rfl
  rw [hJ] at h
  exact h
lemma familyGram_tilt_lower {n:ℕ} (F:Fin n→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) {y z:ℝ} (hy:0<y) (hyz:y<z) (v:Fin n→ℝ) :
    (y^2/z^2)*(v ⬝ᵥ (familyGram stripDensity F F *ᵥ v))≤
      v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v) := by
  have hz:=hy.trans hyz
  have hle:y^2/z^2≤1:=by apply (div_le_one (by positivity)).mpr;nlinarith
  rw [familyGram_quad _ F (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y hz),
    familyGram_quad _ F (fun i j=>stripSpan_actual_pair (hF i) (hF j))]
  have hf:=finiteFamilyCombination_mem_stripSpan hF v
  apply (familySquaredNorm_weight_bounds stripDensity (characteristicRatio y z) (finiteFamilyCombination F v)
    (fun _ hp=>(stripDensity_pos hp).le) (fun p _=>by simpa only [min_eq_right hle,max_eq_left hle] using characteristicRatio_bounds y hz p)
    (by simpa only [pow_two] using stripSpan_actual_pair hf hf)
    (by simpa only [pow_two] using stripSpan_tilt_pair hf hf y hz)).1
/-- Removing the evaluation-at-zero direction changes the characteristic
quotient by at most its single uniform eigenvalue bound. -/
theorem zeroJet_characteristic_sandwich {m N:ℕ} (hm:m+1=2*N) (hN:0<N) {y z:ℝ} (hy:0<y) (hyz:y<z) :
    let w:=fun p=>characteristicRatio y z p*stripDensity p
    let J:=(jetGram (n:=2*N) w (twoKnotLabels N) (twoKnotLabels N)).det/
      (jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N)).det
    let U:=(familyGram w (fun i:Fin m=>zeroJet (twoKnotLabels N) i) (fun i:Fin m=>zeroJet (twoKnotLabels N) i)).det/
      (familyGram stripDensity (fun i:Fin m=>zeroJet (twoKnotLabels N) i) (fun i:Fin m=>zeroJet (twoKnotLabels N) i)).det
    J≤U ∧ (y^2/z^2)*U≤J := by
  classical
  dsimp only
  let b:=twoKnotLabels N
  let F:=fun i:Fin (m+1)=>cosineKernelJet (nodalOrder b i) 0 (b i)
  let w:=fun p=>characteristicRatio y z p*stripDensity p
  let C:=zeroJetMatrix m b
  have hb:b 0=0:=twoKnot_first N hN
  have hF i:F i∈stripKernelSpan (angle^2):=kernel_mem_stripSpan (twoKnot_nonneg N i) (twoKnot_le N i) _
  have hB:(jetGram (n:=m+1) stripDensity b b).PosDef:=by
    rw [hm]
    exact twoJetFamily_posDef N
  have hA:(jetGram (n:=m+1) w b b).PosDef:=by
    rw [hm]
    exact twoJetFamily_tilt_posDef N hy (hy.trans hyz)
  have hCB:(C*jetGram (n:=m+1) stripDensity b b*Cᵀ).PosDef:=by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hB.conjTranspose_mul_mul_same (zeroJetMatrix_transpose_injective m b)
  have hCa:=zeroJet_gram_compression m b hb w (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y (hy.trans hyz))
  have hCb:=zeroJet_gram_compression m b hb stripDensity (fun i j=>stripSpan_actual_pair (hF i) (hF j))
  have h1:=positive_contraction_compression _ _ C hA hB hCB (familyGram_tilt_contraction F hF hy hyz)
  have h2:=positive_compression_codimension _ _ C hA hB hCB (show 0≤y^2/z^2 by positivity) (familyGram_tilt_lower F hF hy hyz)
  change _≤(zeroJetMatrix m b*jetGram (n:=m+1) w b b*(zeroJetMatrix m b)ᵀ).det/
    (zeroJetMatrix m b*jetGram (n:=m+1) stripDensity b b*(zeroJetMatrix m b)ᵀ).det at h1
  change (y^2/z^2)^((m+1)-m)*((zeroJetMatrix m b*jetGram (n:=m+1) w b b*(zeroJetMatrix m b)ᵀ).det/
    (zeroJetMatrix m b*jetGram (n:=m+1) stripDensity b b*(zeroJetMatrix m b)ᵀ).det)≤_ at h2
  rw [←hCa,←hCb,hm] at h1
  rw [←hCa,←hCb,Nat.add_sub_cancel_left,pow_one,hm] at h2
  exact ⟨h1,h2⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology
lemma poleZeroPencil_characteristic_gram {n:ℕ} (b c:ℕ→ℝ) (y z:ℝ) :
    zeroJetPencil (n:=n) (poleAdjustedDensity z) b c (-(y^2))=
      familyGram (fun p=>characteristicRatio y z p*stripDensity p) (fun i:Fin n=>zeroJet b i) (fun i:Fin n=>zeroJet c i) := by
  ext i j
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [zeroJetPencil,familyGram,poleAdjustedDensity,characteristicRatio]
  ring
lemma poleZeroPencil_original_gram {n:ℕ} (b c:ℕ→ℝ) {z:ℝ} (hz:0<z) :
    zeroJetPencil (n:=n) (poleAdjustedDensity z) b c (-(z^2))=
      familyGram stripDensity (fun i:Fin n=>zeroJet b i) (fun i:Fin n=>zeroJet c i) := by
  rw [poleZeroPencil_characteristic_gram]
  congr 1
  funext p
  have hd:(p^2+z^2)≠0:=by positivity
  simp only [characteristicRatio,div_self hd,one_mul]
lemma poleMixedZeroPencil_characteristic_gram {n:ℕ} (b c:ℕ→ℝ) (y z:ℝ) :
    mixedZeroJetPencil (n:=n) (poleAdjustedDensity z) b c (-(y^2))=
      familyGram (fun p=>characteristicRatio y z p*stripDensity p) (fun i:Fin n=>zeroJet b i)
        (fun j:Fin n=>cosineKernelJet (nodalOrder c j) 0 (c j)) := by
  ext i j
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [mixedZeroJetPencil,familyGram,poleAdjustedDensity,characteristicRatio]
  ring
lemma poleMixedZeroPencil_original_gram {n:ℕ} (b c:ℕ→ℝ) {z:ℝ} (hz:0<z) :
    mixedZeroJetPencil (n:=n) (poleAdjustedDensity z) b c (-(z^2))=
      familyGram stripDensity (fun i:Fin n=>zeroJet b i) (fun j:Fin n=>cosineKernelJet (nodalOrder c j) 0 (c j)) := by
  rw [poleMixedZeroPencil_characteristic_gram]
  congr 1
  funext p
  have hd:(p^2+z^2)≠0:=by positivity
  simp only [characteristicRatio,div_self hd,one_mul]
/-- A characteristic product bound for the second nonsymmetric family, uniform over its interior label. -/
theorem second_oblique_characteristic_product_bounds {y z:ℝ} (hy:0<y) (hyz:y<z) :
    ∃ a A:ℝ,0<a ∧ 0<A ∧ ∀ᶠ N:ℕ in atTop,∀ t:ℝ,0<t→t<angle→
      let F:=fun i:Fin (2*N+1)=>zeroJet (extendedKnotLabels N) i
      let G:=fun j:Fin (2*N+1)=>cosineKernelJet (nodalOrder (interiorKnotLabels N t) j) 0 (interiorKnotLabels N t j)
      a*((N:ℝ)+1)^(3*(y-z)/8)≤
        (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F G).det / (familyGram stripDensity F G).det ∧
      (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F G).det / (familyGram stripDensity F G).det≤
        A*((N:ℝ)+1)^(3*(y-z)/8) := by
  obtain ⟨a,A,ha,hA,hbounds⟩:=twoJet_characteristic_bounds hy hyz
  have hz:=hy.trans hyz
  have hl:0<y^2/z^2:=by positivity
  refine ⟨(y^2/z^2)^2*a,A/(y^2/z^2),by positivity,by positivity,?_⟩
  filter_upwards [hbounds,eventually_ge_atTop (1:ℕ)] with N hN hNN
  intro t ht htL
  dsimp only
  have hNpos:0<N:=by omega
  have h:=secondObliqueCharacteristicComparison N hNpos t ht htL y z hy hyz
  dsimp only at h
  simp only [poleZeroPencil_original_gram _ _ hz,poleMixedZeroPencil_original_gram _ _ hz] at h
  simp only [poleZeroPencil_characteristic_gram _ _ y z,poleMixedZeroPencil_characteristic_gram _ _ y z] at h
  have hu:=zeroJet_characteristic_sandwich (m:=2*N-1) (by omega) hNpos hy hyz
  dsimp only at hu
  change a*((N:ℝ)+1)^(3*(y-z)/8)≤
      (jetGram (n:=2*N) (fun p=>characteristicRatio y z p*stripDensity p) (twoKnotLabels N) (twoKnotLabels N)).det/
      (jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N)).det ∧ _ at hN
  constructor
  · calc
      ((y^2/z^2)^2*a)*((N:ℝ)+1)^(3*(y-z)/8)=(y^2/z^2)^2*(a*((N:ℝ)+1)^(3*(y-z)/8)):=by ring
      _≤_:=mul_le_mul_of_nonneg_left (hN.1.trans hu.1) (sq_nonneg _)
      _≤_:=h.1
  · have hh:=(mul_le_mul_of_nonneg_left h.2 hl.le).trans (hu.2.trans hN.2)
    rw [mul_comm] at hh
    have hh' := (le_div_iff₀ hl).mpr hh
    exact hh'.trans_eq (by ring)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory
lemma zeroJet_tilt_det_pos {m N:ℕ} (hm:m+1=2*N) (hN:0<N) {y z:ℝ} (hy:0<y) (hz:0<z) :
    0<(familyGram (fun p=>characteristicRatio y z p*stripDensity p)
      (fun i:Fin m=>zeroJet (twoKnotLabels N) i) (fun i:Fin m=>zeroJet (twoKnotLabels N) i)).det := by
  let b:=twoKnotLabels N
  have hb:b 0=0:=twoKnot_first N hN
  have hF i:(fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) p)∈stripKernelSpan (angle^2):=
    kernel_mem_stripSpan (twoKnot_nonneg N i) (twoKnot_le N i) _
  rw [zeroJet_gram_compression m b hb _ (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y hz)]
  have hA:(jetGram (n:=m+1) (fun p=>characteristicRatio y z p*stripDensity p) b b).PosDef:=by
    rw [hm]
    exact twoJetFamily_tilt_posDef N hy hz
  have hC:(zeroJetMatrix m b*jetGram (n:=m+1) (fun p=>characteristicRatio y z p*stripDensity p) b b*(zeroJetMatrix m b)ᵀ).PosDef:=by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hA.conjTranspose_mul_mul_same (zeroJetMatrix_transpose_injective m b)
  exact hC.det_pos
lemma secondOblique_expansion_aux {m N:ℕ} (hm:m+1=2*N) (hN:0<N) {t y z:ℝ}
    (ht:0<t) (htL:t<angle) (hz:0<z) (hzy:z<y) :
    let S:=(zeroJetPencil (n:=m) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(y^2))).det/
      (zeroJetPencil (n:=m) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(z^2))).det
    let Q:=(mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) (-(y^2))).det/
      (mixedZeroJetPencil (n:=m+2) (poleAdjustedDensity z) (extendedKnotLabels N) (interiorKnotLabels N t) (-(z^2))).det
    S≤Q ∧ Q≤(y^2/z^2)^2*S := by
  have hy:=hz.trans hzy
  have hi (i j:Fin (m+2)):IntegrableOn
      (fun p=>secondLeftFlag m N i (p^2)*secondRightFlag m N t j (p^2)*poleAdjustedDensity z p) (Set.Ioi 0):=by
    simpa only [pow_zero,one_mul] using stripSpan_pair_integrable hz 0 (secondLeft_mem m N i) (secondRight_mem m N j ht htL)
  have h := unorientedPencil_two_steps (secondLeftFlag m N) (secondRightFlag m N t) (poleAdjustedDensity z)
    (secondLeft_nonvanishing hm hN) (secondRight_nonvanishing hm hN ht htL)
    (fun i=>stripSpan_continuous (secondLeft_mem m N i)) (fun i=>stripSpan_continuous (secondRight_mem m N i ht htL))
    (fun _ hp=>poleAdjustedDensity_pos hz hp) hi
    (fun i j=>stripSpan_pair_integrable hz 2 (secondLeft_mem m N i) (secondRight_mem m N j ht htL))
    (sq_pos_of_pos hz) (by nlinarith : z^2<y^2)
  rw [secondChain_pencil_ratio hm hN ht htL hz,secondChain_bottom_pencil,secondChain_bottom_pencil] at h
  have hdet (u:ℝ) (hu:0<u):0<(zeroJetPencil (n:=m) (poleAdjustedDensity z) (twoKnotLabels N) (twoKnotLabels N) (-(u^2))).det:=by
    rw [poleZeroPencil_characteristic_gram]
    exact zeroJet_tilt_det_pos hm hN hu hz
  have hS:=div_pos (hdet z hz) (hdet y hy)
  have hl:0<(z^2/y^2)^2:=by positivity
  have hQ:(0:ℝ)<_ := (mul_pos hl hS).trans_le h.1
  have hr:=positive_ratio_reversal hS hQ hl h.1 h.2
  dsimp only
  simpa only [←inv_pow,inv_div] using hr
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory
lemma familyGram_expansion_lower {n:ℕ} (F:Fin n→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) {y z:ℝ} (hz:0<z) (hzy:z≤y) (v:Fin n→ℝ) :
    (1:ℝ)*(v ⬝ᵥ (familyGram stripDensity F F *ᵥ v))≤
      v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v) := by
  have hle:1≤y^2/z^2:=by apply (le_div_iff₀ (by positivity)).mpr;nlinarith
  rw [familyGram_quad _ F (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y hz),
    familyGram_quad _ F (fun i j=>stripSpan_actual_pair (hF i) (hF j))]
  have hf:=finiteFamilyCombination_mem_stripSpan hF v
  apply (familySquaredNorm_weight_bounds stripDensity (characteristicRatio y z) (finiteFamilyCombination F v)
    (fun _ hp=>(stripDensity_pos hp).le) (fun p _=>by simpa only [min_eq_left hle,max_eq_right hle] using characteristicRatio_bounds y hz p)
    (by simpa only [pow_two] using stripSpan_actual_pair hf hf)
    (by simpa only [pow_two] using stripSpan_tilt_pair hf hf y hz)).1
/-- Removing the evaluation direction under an expanding characteristic
factor only decreases the characteristic determinant quotient. -/
theorem zeroJet_expansion_upper {m N:ℕ} (hm:m+1=2*N) (hN:0<N) {y z:ℝ} (hz:0<z) (hzy:z≤y) :
    (familyGram (fun p=>characteristicRatio y z p*stripDensity p)
      (fun i:Fin m=>zeroJet (twoKnotLabels N) i) (fun i:Fin m=>zeroJet (twoKnotLabels N) i)).det/
    (familyGram stripDensity (fun i:Fin m=>zeroJet (twoKnotLabels N) i) (fun i:Fin m=>zeroJet (twoKnotLabels N) i)).det ≤
    (jetGram (n:=2*N) (fun p=>characteristicRatio y z p*stripDensity p) (twoKnotLabels N) (twoKnotLabels N)).det/
    (jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N)).det := by
  classical
  let b:=twoKnotLabels N
  let F:=fun i:Fin (m+1)=>cosineKernelJet (nodalOrder b i) 0 (b i)
  let w:=fun p=>characteristicRatio y z p*stripDensity p
  let C:=zeroJetMatrix m b
  have hb:b 0=0:=twoKnot_first N hN
  have hF i:F i∈stripKernelSpan (angle^2):=kernel_mem_stripSpan (twoKnot_nonneg N i) (twoKnot_le N i) _
  have hB:(jetGram (n:=m+1) stripDensity b b).PosDef:=by rw [hm];exact twoJetFamily_posDef N
  have hA:(jetGram (n:=m+1) w b b).PosDef:=by rw [hm];exact twoJetFamily_tilt_posDef N (hz.trans_le hzy) hz
  have hCB:(C*jetGram (n:=m+1) stripDensity b b*Cᵀ).PosDef:=by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hB.conjTranspose_mul_mul_same (zeroJetMatrix_transpose_injective m b)
  have hCa:=zeroJet_gram_compression m b hb w (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y hz)
  have hCb:=zeroJet_gram_compression m b hb stripDensity (fun i j=>stripSpan_actual_pair (hF i) (hF j))
  have h2:=positive_compression_codimension _ _ C hA hB hCB (by norm_num : (0:ℝ)≤1) (familyGram_expansion_lower F hF hz hzy)
  simp only [one_pow,one_mul] at h2
  change (zeroJetMatrix m b*jetGram (n:=m+1) w b b*(zeroJetMatrix m b)ᵀ).det/
    (zeroJetMatrix m b*jetGram (n:=m+1) stripDensity b b*(zeroJetMatrix m b)ᵀ).det≤_ at h2
  rw [←hCa,←hCb,hm] at h2
  exact h2
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology
/-- A moving-parameter characteristic bound for the second nonsymmetric family. -/
theorem second_oblique_growing_product_bound :
    ∃ D:ℕ,0<D ∧ ∃ c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠ N:ℕ in atTop,
      ∀ y z:ℝ,1≤z→z<y→y^2≤2*z^2→1/2≤c*y/Real.pi→
      ∀ t:ℝ,0<t→t<angle→
      let F:=fun i:Fin (2*N+1)=>zeroJet (extendedKnotLabels N) i
      let G:=fun j:Fin (2*N+1)=>cosineKernelJet (nodalOrder (interiorKnotLabels N t) j) 0 (interiorKnotLabels N t j)
      (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F G).det /
      (familyGram stripDensity F G).det ≤
      16*(1+C*z^4*((D*N:ℕ)+1:ℝ)^3*(4*((D*N:ℕ)+1:ℝ))^(2*c*y/Real.pi+1)) := by
  obtain ⟨D,hD,htwo⟩:=twoJet_polynomial_expansion_uniform
  obtain ⟨c,C,hc,hC,hpoly⟩:=strip_polynomial_square_product_uniform
  refine ⟨D,hD,c,C,hc,hC,?_⟩
  filter_upwards [htwo,eventually_ge_atTop (1:ℕ)] with N hN hNN
  intro y z hz hzy hyz hs t ht htL
  dsimp only
  have hz0:0<z:=by linarith
  have hy0:=hz0.trans hzy
  have hNp:0<N:=by omega
  have hm:(2*N-1)+1=2*N:=by omega
  have hn:(2*N-1)+2=2*N+1:=by omega
  have h:=secondOblique_expansion_aux hm hNp ht htL hz0 hzy
  dsimp only at h
  rw [hn] at h
  simp only [poleZeroPencil_original_gram _ _ hz0,poleMixedZeroPencil_original_gram _ _ hz0] at h
  simp only [poleZeroPencil_characteristic_gram _ _ y z,poleMixedZeroPencil_characteristic_gram _ _ y z] at h
  have hu:=zeroJet_expansion_upper hm hNp hz0 hzy.le
  have hj:=hN y z hz0 hzy.le hyz
  change (jetGram (n:=2*N) (fun p=>characteristicRatio y z p*stripDensity p) (twoKnotLabels N) (twoKnotLabels N)).det /
      (jetGram (n:=2*N) stripDensity (twoKnotLabels N) (twoKnotLabels N)).det ≤ _ at hj
  have hbase:=zeroJet_tilt_det_pos hm hNp hz0 hz0
  have he:(fun p=>characteristicRatio z z p*stripDensity p)=stripDensity:=by
    funext p
    have hd:p^2+z^2≠0:=by positivity
    simp only [characteristicRatio,div_self hd,one_mul]
  rw [he] at hbase
  have hU:0≤(familyGram (fun p=>characteristicRatio y z p*stripDensity p)
      (fun i:Fin (2*N-1)=>zeroJet (twoKnotLabels N) i) (fun i:Fin (2*N-1)=>zeroJet (twoKnotLabels N) i)).det/
    (familyGram stripDensity (fun i:Fin (2*N-1)=>zeroJet (twoKnotLabels N) i) (fun i:Fin (2*N-1)=>zeroJet (twoKnotLabels N) i)).det:=
    (div_pos (zeroJet_tilt_det_pos hm hNp hy0 hz0) hbase).le
  have hratio:y^2/z^2≤2:=(div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hratio0:0≤y^2/z^2:=by positivity
  have hratio2:(y^2/z^2)^2≤4:=by nlinarith
  have ho:=(polynomial_characteristic_le_one_square (D*N) hy0 hz0).trans
    (show 1 + _ ≤ 1+C*z^4*((D*N:ℕ)+1:ℝ)^3*(4*((D*N:ℕ)+1:ℝ))^(2*c*y/Real.pi+1) by
      linarith [hpoly y z hz hs (D*N)])
  have hh:=(h.2.trans (mul_le_mul_of_nonneg_right hratio2 hU)).trans
    (mul_le_mul_of_nonneg_left (hu.trans hj) (by norm_num : (0:ℝ)≤4))
  have hf:=mul_le_mul_of_nonneg_left ho (by norm_num : (0:ℝ)≤16)
  calc
    _≤4*(4*((monomialGram (D*N) (fun p=>characteristicRatio y z p*stripDensity p)).det /
        (monomialGram (D*N) stripDensity).det)):=hh
    _=16*((monomialGram (D*N) (fun p=>characteristicRatio y z p*stripDensity p)).det /
        (monomialGram (D*N) stripDensity).det):=by ring
    _≤_:=hf
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology Asymptotics
/-- A scalar estimate for moving-parameter characteristic products with exponent `3/4`. -/
lemma rpow_log_isLittleO_id {r:ℝ} (hr:r<1) :
    (fun x:ℝ=>x^r*log x)=o[atTop] fun x=>x := by
  have h:=(isLittleO_log_rpow_atTop (show 0<1-r by linarith)).mul_isBigO
    (isBigO_refl (fun x:ℝ=>x^r) atTop)
  apply h.congr'
  · exact Eventually.of_forall (fun x=>mul_comm _ _)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [←rpow_add hx,show 1-r+r=(1:ℝ) by ring,rpow_one]
lemma rpow_isLittleO_id {r:ℝ} (hr:r<1) :
    (fun x:ℝ=>x^r)=o[atTop] fun x=>x := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact fun h=>(hx.ne' h).elim
  · apply (tendsto_rpow_neg_atTop (show 0<1-r by linarith)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [show -(1-r)=r-1 by ring,rpow_sub hx,rpow_one]
lemma log_majorant_isLittleO_id (A a b c d r:ℝ) (hr:r<1) :
    (fun x:ℝ=>log A+a*log x+(b*x^r+c)*(log d+log x))=o[atTop] fun x=>x := by
  have h0:=isLittleO_const_id_atTop (log A)
  have h1:=isLittleO_log_id_atTop.const_mul_left a
  have h2:=(rpow_isLittleO_id hr).const_mul_left (b*log d)
  have h3:=(rpow_log_isLittleO_id hr).const_mul_left b
  have h4:=isLittleO_const_id_atTop (c*log d)
  have h5:=isLittleO_log_id_atTop.const_mul_left c
  have h:=((((h0.add h1).add h2).add h3).add h4).add h5
  apply h.congr'
  · exact Eventually.of_forall (fun x=>by dsimp;ring)
  · exact Eventually.of_forall (fun _=>rfl)
/-- Polynomial power products are exponentially negligible at every fixed sublinear moving exponent. -/
theorem polynomial_power_product_subexponential {A d r:ℝ} (hA:0<A) (hd:0<d) (hr:r<1)
    (a b c:ℝ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ x:ℝ in atTop,A*x^a*(d*x)^(b*x^r+c)≤exp (ε*x) := by
  have hlim:=(log_majorant_isLittleO_id A a b c d r hr).tendsto_div_nhds_zero
  filter_upwards [hlim.eventually_le_const hε,eventually_gt_atTop (0:ℝ)] with x h hx
  have hpos:0<A*x^a*(d*x)^(b*x^r+c):=by positivity
  apply (log_le_iff_le_exp hpos).mp
  rw [log_mul (by positivity : A*x^a≠0) (by positivity),log_rpow (by positivity),
    log_mul hA.ne' (by positivity),log_rpow hx,log_mul hd.ne' hx.ne']
  exact (div_le_iff₀ hx).mp h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
/-- The characteristic product is `exp(o(N))` at a moving pole of order `N^(3/4)`. -/
theorem moving_majorant_subexponential (D:ℕ) {C k ε:ℝ} (hC:0≤C) (hk:0≤k) (hε:0<ε) :
    ∀ᶠ N:ℕ in atTop,
      16*(1+C*((N:ℝ)^(3/4:ℝ))^4*((D*N:ℕ)+1:ℝ)^3*
        (4*((D*N:ℕ)+1:ℝ))^(k*(N:ℝ)^(3/4:ℝ)+1)) ≤ exp (ε*N) := by
  let T:ℝ:=(D:ℝ)+1
  have hT:1≤T:=by dsimp [T]; have h:=Nat.cast_nonneg (α:=ℝ) D; linarith
  have hA:0<16*(1+C*T^3):=by positivity
  have hd:0<4*T:=by positivity
  have hlim:=(tendsto_natCast_atTop_atTop : Tendsto (fun N:ℕ=>(N:ℝ)) atTop atTop).eventually
    (polynomial_power_product_subexponential hA hd (by norm_num : (3/4:ℝ)<1) 7 k 1 hε)
  filter_upwards [hlim,eventually_ge_atTop (1:ℕ)] with N hN hNN
  have hx:1≤(N:ℝ):=by exact_mod_cast hNN
  have hx0:0<(N:ℝ):=by linarith
  have hroot:(N:ℝ)^(3/4:ℝ)≤(N:ℝ):=by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx (by norm_num : (3/4:ℝ)≤1)
  have ht:((D*N:ℕ)+1:ℝ)≤T*N:=by
    push_cast
    dsimp [T]
    nlinarith
  have he:0≤k*(N:ℝ)^(3/4:ℝ)+1:=by positivity
  have hb:1≤4*T*(N:ℝ):=by nlinarith
  let F:ℝ:=(N:ℝ)^7*(4*T*(N:ℝ))^(k*(N:ℝ)^(3/4:ℝ)+1)
  have hF:1≤F:=by
    have h1:1≤(N:ℝ)^7:=one_le_pow₀ hx
    have h2:=one_le_rpow hb he
    dsimp [F]
    nlinarith
  have hu:C*((N:ℝ)^(3/4:ℝ))^4*((D*N:ℕ)+1:ℝ)^3*
        (4*((D*N:ℕ)+1:ℝ))^(k*(N:ℝ)^(3/4:ℝ)+1)≤C*T^3*F:=by
    calc
      _≤C*(N:ℝ)^4*(T*N)^3*(4*T*(N:ℝ))^(k*(N:ℝ)^(3/4:ℝ)+1):=by
        have hbase:4*((D*N:ℕ)+1:ℝ)≤4*T*(N:ℝ):=by linarith
        have hp:=rpow_le_rpow (by positivity : (0:ℝ)≤4*((D*N:ℕ)+1:ℝ)) hbase he
        have hz4:=pow_le_pow_left₀ (rpow_nonneg (Nat.cast_nonneg N) _) hroot 4
        have ht3:=pow_le_pow_left₀ (by positivity : (0:ℝ)≤((D*N:ℕ)+1:ℝ)) ht 3
        have hprod:=mul_le_mul (mul_le_mul_of_nonneg_left hz4 hC) ht3 (by positivity) (by positivity)
        exact mul_le_mul hprod hp (by positivity) (by positivity)
      _=C*T^3*F:=by dsimp [F];ring
  have hf:16*(1+C*T^3*F)≤16*(1+C*T^3)*F:=by nlinarith
  have hmajor:16*(1+C*((N:ℝ)^(3/4:ℝ))^4*((D*N:ℕ)+1:ℝ)^3*
      (4*((D*N:ℕ)+1:ℝ))^(k*(N:ℝ)^(3/4:ℝ)+1))≤16*(1+C*T^3)*F:=by
    nlinarith
  have hN':16*(1+C*T^3)*F≤exp (ε*N):=by
    rw [show (N:ℝ)^(7:ℝ)=(N:ℝ)^(7:ℕ) from rpow_natCast _ _] at hN
    simpa only [F,mul_assoc] using hN
  exact hmajor.trans hN'
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Real Filter Topology
noncomputable def movingPole (N:ℕ) : ℝ := (N:ℝ)^(3/4:ℝ)
lemma movingPole_conditions {c:ℝ} (hc:0 < c) :
    ∀ᶠ N:ℕ in atTop, 1 ≤ movingPole N ∧ movingPole N < sqrt 2*movingPole N ∧
      (sqrt 2*movingPole N)^2 ≤ 2*(movingPole N)^2 ∧ 1/2 ≤ c*(sqrt 2*movingPole N)/Real.pi := by
  have hs:sqrt 2 > 1:=by nlinarith [sq_sqrt (by norm_num : (0:ℝ) ≤ 2),sqrt_nonneg (2:ℝ)]
  have hd:0 < 2*c*sqrt 2:=by positivity
  have hlim: Tendsto movingPole atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 1,hlim.eventually_ge_atTop (Real.pi/(2*c*sqrt 2))] with N hN hB
  have hp:0 < movingPole N:=by linarith
  refine ⟨hN,by nlinarith,?_,?_⟩
  · rw [mul_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · apply (le_div_iff₀ pi_pos).mpr
    have h:Real.pi ≤ movingPole N*(2*c*sqrt 2):=(div_le_iff₀ hd).mp hB
    nlinarith
/-- First actual two-endpoint ensemble has exp(o(N)) characteristic moment
at y²=2z²=2N^(3/2), uniformly in both interior labels. -/
theorem first_oblique_moving_subexponential {ε:ℝ} (hε:0 < ε) :
    ∀ᶠ N:ℕ in atTop,∀ s t:ℝ,0 < s→s < angle→0 < t→t < angle→
      (jetGram (n:=2*N+1) (fun p=>characteristicRatio (sqrt 2*movingPole N) (movingPole N) p*stripDensity p)
        (interiorKnotLabels N s) (interiorKnotLabels N t)).det /
      (jetGram (n:=2*N+1) stripDensity (interiorKnotLabels N s) (interiorKnotLabels N t)).det  ≤  exp (ε*N) := by
  obtain ⟨D,hD,c,C,hc,hC,hbound⟩:=first_oblique_growing_product_bound
  let k:ℝ:=2*c*sqrt 2/Real.pi
  have hk:0 ≤ k:=by dsimp [k];positivity
  have hmajor:=moving_majorant_subexponential D hC.le hk hε
  filter_upwards [hbound,hmajor,movingPole_conditions hc] with N hN hM hP
  intro s t hs hsL ht htL
  have hh:=hN (sqrt 2*movingPole N) (movingPole N) hP.1 hP.2.1.le hP.2.2.1 hP.2.2.2 s t hs hsL ht htL
  have he:2*c*(sqrt 2*movingPole N)/Real.pi+1=k*movingPole N+1:=by dsimp [k];ring
  rw [he] at hh
  have hnonneg:0 ≤ 1+C*(movingPole N)^4*((D*N:ℕ)+1:ℝ)^3*(4*((D*N:ℕ)+1:ℝ))^(k*movingPole N+1):=by positivity
  exact (hh.trans (mul_le_mul_of_nonneg_right (by norm_num : (8:ℝ) ≤ 16) hnonneg)).trans hM
/-- A subexponential moving-parameter bound for the second nonsymmetric family. -/
theorem second_oblique_moving_subexponential {ε:ℝ} (hε:0 < ε) :
    ∀ᶠ N:ℕ in atTop,∀ t:ℝ,0 < t→t < angle→
      let F:=fun i:Fin (2*N+1)=>zeroJet (extendedKnotLabels N) i
      let G:=fun j:Fin (2*N+1)=>cosineKernelJet (nodalOrder (interiorKnotLabels N t) j) 0 (interiorKnotLabels N t j)
      (familyGram (fun p=>characteristicRatio (sqrt 2*movingPole N) (movingPole N) p*stripDensity p) F G).det /
      (familyGram stripDensity F G).det  ≤  exp (ε*N) := by
  obtain ⟨D,hD,c,C,hc,hC,hbound⟩:=second_oblique_growing_product_bound
  let k:ℝ:=2*c*sqrt 2/Real.pi
  have hk:0 ≤ k:=by dsimp [k];positivity
  have hmajor:=moving_majorant_subexponential D hC.le hk hε
  filter_upwards [hbound,hmajor,movingPole_conditions hc] with N hN hM hP
  intro t ht htL
  have hh:=hN (sqrt 2*movingPole N) (movingPole N) hP.1 hP.2.1 hP.2.2.1 hP.2.2.2 t ht htL
  have he:2*c*(sqrt 2*movingPole N)/Real.pi+1=k*movingPole N+1:=by dsimp [k];ring
  dsimp only at hh ⊢
  rw [he] at hh
  exact hh.trans hM
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI

import OAI.Analysis.Littlewood.SlotGraph

namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

def chunkCount (B q : ℕ) : ℕ := (q-1)/B

lemma chunkCount_bounds {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    B*chunkCount B q<q ∧ q≤B*(chunkCount B q+1) := by
  have hm := Nat.mod_lt (q-1) hB
  have he := Nat.mod_add_div (q-1) B
  dsimp [chunkCount]
  constructor
  · have hd := Nat.mul_div_le (q-1) B
    omega
  · nlinarith only [hm,he,show q-1+1=q by omega]

lemma chunkCount_pos {B q : ℕ} (hB : 0<B) (hq : B<q) : 0<chunkCount B q := by
  exact Nat.div_pos (by omega) hB

lemma chunkCount_ratio_error {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    |(chunkCount B q : ℝ)/q-1/(B : ℝ)|≤1/(q : ℝ) := by
  obtain ⟨hlo,hhi⟩ := chunkCount_bounds hB hq
  have hB' : (0 : ℝ)<B := by exact_mod_cast hB
  have hq' : (0 : ℝ)<q := by exact_mod_cast hq
  have hlo' : (B : ℝ)*chunkCount B q≤q := by exact_mod_cast hlo.le
  have hhi' : (q : ℝ)≤B*(chunkCount B q+1) := by exact_mod_cast hhi
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hB' hq')).mp
    field_simp
    nlinarith only [hhi']
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hB' hq')).mp
    field_simp
    nlinarith only [hlo']

lemma chunkCount_ratio_tendsto {B : ℕ} (hB : 0<B) :
    Tendsto (fun q : ℕ ↦ (chunkCount B q : ℝ)/q) atTop (𝓝 (1/(B : ℝ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun q ↦ norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    simpa only [Real.norm_eq_abs] using chunkCount_ratio_error hB hq
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

def packingAV (r L R q : ℕ) : ℝ :=
  let k := (chunkCount (2*R*L) q : ℝ)/(q : ℝ)
  let u := 1/(q : ℝ)
  3*(2*(((r-1 : ℕ) : ℝ)*(1-2*((R : ℝ)-2)*L*k)+
    2*((r-1 : ℕ) : ℝ)^2*(2*(R : ℝ)*L+1)*u)+
    ((r-1 : ℕ) : ℝ)^2*(1-2*((R : ℝ)-2)*L*k+2*((R : ℝ)-2)*L*u))

def packingNV (r L R q : ℕ) : ℝ :=
  (r : ℝ)*((R : ℝ)-1)*((chunkCount (2*R*L) q : ℝ)/(q : ℝ))

def packingALimit (r R : ℕ) : ℝ :=
  6*(2*((r-1 : ℕ) : ℝ)+((r-1 : ℕ) : ℝ)^2)/(R : ℝ)

def packingNLimit (r L R : ℕ) : ℝ :=
  (r : ℝ)*(1-1/(R : ℝ))/(2*(L : ℝ))

lemma packingAV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) :
    Tendsto (packingAV r L R) atTop (𝓝 (packingALimit r R)) := by
  have hk := chunkCount_ratio_tendsto (show 0<2*R*L by positivity)
  have hq : Tendsto (fun q : ℕ ↦ 1/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  let a := ((r-1 : ℕ) : ℝ)
  let c := 2*((R : ℝ)-2)*L
  have hb := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (hk.const_mul c)
  have ht := (((hb.const_mul a).add (hq.const_mul (2*a^2*(2*(R : ℝ)*L+1)))).const_mul 2 |>.add
    ((hb.add (hq.const_mul c)).const_mul (a^2))).const_mul 3
  have he : 3*(2*(a*(1-c*(1/((2*R*L : ℕ) : ℝ)))+
      2*a^2*(2*(R : ℝ)*L+1)*0)+a^2*(1-c*(1/((2*R*L : ℕ) : ℝ))+c*0)) =
      packingALimit r R := by
    dsimp [a,c,packingALimit]
    have hRn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
    have hLn : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
    ring
  rw [he] at ht
  exact ht

lemma packingNV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) :
    Tendsto (packingNV r L R) atTop (𝓝 (packingNLimit r L R)) := by
  have hk := chunkCount_ratio_tendsto (show 0<2*R*L by positivity)
  have ht := hk.const_mul ((r : ℝ)*((R : ℝ)-1))
  have he : (r : ℝ)*((R : ℝ)-1)*(1/((2*R*L : ℕ) : ℝ))=packingNLimit r L R := by
    dsimp [packingNLimit]
    have hRn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
    have hLn : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp

  rw [he] at ht
  exact ht

lemma packingALimit_tendsto (r : ℕ) :
    Tendsto (packingALimit r) atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

lemma packingNLimit_tendsto (r L : ℕ) :
    Tendsto (packingNLimit r L) atTop (𝓝 ((r : ℝ)/(2*L))) := by
  have hq : Tendsto (fun R : ℕ ↦ 1/(R : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  unfold packingNLimit
  simpa only [sub_zero, mul_one] using
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).const_mul (r : ℝ)).div_const (2*L)

def packingBV (r L R : ℕ) (e p : ℝ) (q : ℕ) : ℝ :=
  (r : ℝ)*max (packingAV r L R q) 0/(e*p/2)^2

def packingBLimit (r R : ℕ) (e p : ℝ) : ℝ :=
  (r : ℝ)*packingALimit r R/(e*p/2)^2

lemma packingBV_nonneg (r L R q : ℕ) (e p : ℝ) :
    0≤packingBV r L R e p q := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) (sq_nonneg _)

lemma packingBV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) (e p : ℝ) :
    Tendsto (packingBV r L R e p) atTop (𝓝 (packingBLimit r R e p)) := by
  have hA : 0≤packingALimit r R := by unfold packingALimit; positivity
  have h := (((packingAV_tendsto (r := r) hL hR).max
    (tendsto_const_nhds (x := (0 : ℝ)))).const_mul (r : ℝ)).div_const ((e*p/2)^2)
  unfold packingBV packingBLimit
  simpa only [max_eq_left hA] using h

lemma packingBLimit_tendsto (r : ℕ) (e p : ℝ) :
    Tendsto (fun R ↦ packingBLimit r R e p) atTop (𝓝 (0 : ℝ)) := by
  have h := ((packingALimit_tendsto r).const_mul (r : ℝ)).div_const ((e*p/2)^2)
  unfold packingBLimit
  simpa only [mul_zero,zero_div] using h

lemma packing_choose_R {r L : ℕ} (hr : 0<r) (hL : 0<L)
    {e p η t : ℝ} (he : 0<e) (hp : 0<p)
    (hmargin : (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L))) :
    ∃ R : ℕ, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by
  have hNpos : (0 : ℝ)<(r : ℝ)/(2*L) := by positivity
  have hNlt : (r : ℝ)/(2*L)<r := by
    have hl : (1 : ℝ)≤L := by exact_mod_cast hL
    have hr' : (0 : ℝ)<r := by exact_mod_cast hr
    apply (div_lt_iff₀ (by positivity : (0 : ℝ)<2*L)).mpr
    nlinarith
  have hN := packingNLimit_tendsto r L
  have hB := packingBLimit_tendsto r e p
  have hS := hN.sub hB
  have hSp : Tendsto (fun R ↦ packingNLimit r L R-packingBLimit r R e p) atTop
      (𝓝 ((r : ℝ)/(2*L))) := by simpa using hS
  have hev : ∀ᶠ R : ℕ in atTop, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by
    filter_upwards [eventually_ge_atTop 3,
      hB.eventually (gt_mem_nhds (show (0 : ℝ)<e*p/2 by positivity)),
      hSp.eventually (lt_mem_nhds hNpos),hN.eventually (gt_mem_nhds hNlt),
      (hSp.const_mul (1-η)).eventually (lt_mem_nhds hmargin)] with R hR h1 h2 h3 h4
    exact ⟨hR,h1,h2,h3,h4⟩
  exact hev.exists

lemma packing_eventual_parameters {r L R : ℕ} (hL : 0<L) (hR : 0<R)
    {e p η t T : ℝ} (he : 0<e) (hp : 0<p)
    (hB : packingBLimit r R e p<e*p/2)
    (hS : 0<packingNLimit r L R-packingBLimit r R e p)
    (hN : packingNLimit r L R<(r : ℝ))
    (hM : (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p)) :
    ∀ᶠ q : ℕ in atTop,
      1/(q : ℝ)≤e*p ∧ T/(q : ℝ)≤p ∧
      T/(q : ℝ)≤packingNV r L R q-packingBV r L R e p q ∧
      packingBV r L R e p q≤e*p/2 ∧ packingNV r L R q≤(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNV r L R q-packingBV r L R e p q) := by
  have hNt := packingNV_tendsto (r := r) hL hR
  have hBt := packingBV_tendsto (r := r) hL hR e p
  have hSt := hNt.sub hBt
  have hq : Tendsto (fun q : ℕ ↦ 1/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hT : Tendsto (fun q : ℕ ↦ T/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hq.eventually (gt_mem_nhds (mul_pos he hp)),
    hT.eventually (gt_mem_nhds hp),hT.eventually_lt hSt hS,
    hBt.eventually (gt_mem_nhds hB),hNt.eventually (gt_mem_nhds hN),
    (hSt.const_mul (1-η)).eventually (lt_mem_nhds hM)] with q h1 h2 h3 h4 h5 h6
  exact ⟨h1.le,h2.le,h3.le,h4.le,h5.le,h6⟩

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

lemma concrete_slot_variance_le_av {r q : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (R : ℕ) (i₀ : Fin r) (hR : 2≤R)
    (hq' : 2*R*periodLength (oddLengths d)<q)
    {V : Type uV} [AddCommGroup V] [Module (ZMod q) V] [Fintype V] [DecidableEq V]
    (g : Fin r → V →ₗ[ZMod q] ZMod q)
    (hg : ∀ i, Function.Surjective (g i))
    (hpair : ∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) (i : Fin r) :
    let K := chunkCount (2*R*periodLength (oddLengths d)) q
    avg (fun ω : SlotChoices d K ↦ avg (fun s : ZMod q ↦
      (slotDensity g (fun j t ↦ slotHit d R K q j ω t) i s-
        (1/(2*periodLength (oddLengths d) : ℝ))^(r-1))^2)) ≤
      packingAV r (periodLength (oddLengths d)) R q := by
  dsimp only
  let L := periodLength (oddLengths d)
  let K := chunkCount (2*R*L) q
  have hL : 0<L := periodLength_pos d i₀
  have hq0 : 0<q := (Fact.out : q.Prime).pos
  have hq : 2*(K*(R*L))<q := by
    have h := (chunkCount_bounds (show 0<2*R*L by positivity) hq0).1
    dsimp [K]
    nlinarith only [h]
  have hK : 0<K := chunkCount_pos (by positivity) hq'
  have h := concrete_slot_variance d R K i₀ hK hq g hg hpair i
  have hcat : (catalogSet d R K q).card≤q := by
    simpa only [ZMod.card] using (Finset.card_le_univ (catalogSet d R K q))
  have hc := catalogSet_card d R K q i₀ hq
  have hs : ((shortResidues q (R*L)).card : ℝ)≤2*(R : ℝ)*L+1 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_assoc] using
      (Nat.cast_le.mpr (shortResidues_card q (R*L)) : ((shortResidues q (R*L)).card : ℝ)≤((2*(R*L)+1 : ℕ) : ℝ))
  have hR2 : ((R-2 : ℕ) : ℝ)=(R : ℝ)-2 := by rw [Nat.cast_sub hR]; norm_num
  have hqpos : (0 : ℝ)<q := by exact_mod_cast hq0
  apply h.trans
  rw [Nat.cast_add,Nat.cast_sub hcat]
  simp only [hc,Nat.cast_mul,Nat.cast_ofNat,hR2]
  change 3*(2*(((r-1 : ℕ) : ℝ)*((q : ℝ)-2*(K : ℝ)*(((R : ℝ)-2)*L))/q+
      2*((r-1 : ℕ) : ℝ)^2*((shortResidues q (R*L)).card : ℝ)/q)+
      ((r-1 : ℕ) : ℝ)^2*((q : ℝ)-2*(K : ℝ)*(((R : ℝ)-2)*L)+2*(((R : ℝ)-2)*L))/q)≤_
  have hshort := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ)≤2*((r-1 : ℕ) : ℝ)^2)) hqpos.le
  dsimp [packingAV]
  change _≤3*(2*(((r-1 : ℕ) : ℝ)*(1-2*((R : ℝ)-2)*L*((K : ℝ)/q))+
      2*((r-1 : ℕ) : ℝ)^2*(2*(R : ℝ)*L+1)*(1/q))+
      ((r-1 : ℕ) : ℝ)^2*(1-2*((R : ℝ)-2)*L*((K : ℝ)/q)+2*((R : ℝ)-2)*L*(1/q)))
  have hqne := hqpos.ne'
  field_simp at hshort ⊢
  nlinarith only [hshort]

lemma concrete_slot_nv {r q R : ℕ} [Fact q.Prime]
    (d : Fin r → ℕ) (i₀ : Fin r) (hR : 1≤R)
    (ω : SlotChoices d (chunkCount (2*R*periodLength (oddLengths d)) q)) :
    ((slotVertices (fun i t ↦ slotHit d R
      (chunkCount (2*R*periodLength (oddLengths d)) q) q i ω t)).card : ℝ)=
      (q : ℝ)*packingNV r (periodLength (oddLengths d)) R q := by
  have hL := periodLength_pos d i₀
  have hq0 := (Fact.out : q.Prime).pos
  have hq : 2*(chunkCount (2*R*periodLength (oddLengths d)) q*
      (R*periodLength (oddLengths d)))<q := by
    have h := (chunkCount_bounds (show 0<2*R*periodLength (oddLengths d) by positivity) hq0).1
    nlinarith only [h]
  rw [concrete_slot_vertices_card d R _ hq]
  simp only [Nat.cast_mul,Nat.cast_sub hR,Nat.cast_one]
  unfold packingNV
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hq0.ne'
  field_simp

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

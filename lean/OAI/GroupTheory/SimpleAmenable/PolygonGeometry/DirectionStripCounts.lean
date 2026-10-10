import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagSiteCounts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DirectionStripCounts
open Classical

noncomputable def cutCoordinates (a : ℕ) (j : Fin 4) : (CutRing×CutRing) ≃ (CutRing×CutRing) where
  toFun p := ![p,(p.2,p.1),(p.2-cutTau^a*p.1,p.1),(p.1-cutTau^a*p.2,p.2)] j
  invFun q := ![q,(q.2,q.1),(q.2,q.1+cutTau^a*q.2),(q.1+cutTau^a*q.2,q.2)] j
  left_inv p := by fin_cases j <;> simp
  right_inv p := by fin_cases j <;> simp

@[simp] theorem cutCoordinates_fst (a : ℕ) (j : Fin 4) (p : CutRing×CutRing) :
    (cutCoordinates a j p).1=integralCutForm a j p := by
  fin_cases j <;> simp [cutCoordinates,integralCutForm]

theorem cutCoordinates_conjugate_bound (a : ℕ) (j : Fin 4) (p : CutRing×CutRing)
    {R : ℝ} (hR : 0 ≤ R) (hx : |conjugate p.1| ≤ R) (hy : |conjugate p.2| ≤ R) :
    |conjugate (cutCoordinates a j p).1| ≤ (1+|conjugate (cutTau^a)|)*R := by
  have hmulx := mul_le_mul_of_nonneg_left hx (abs_nonneg (conjugate (cutTau^a)))
  have hmuly := mul_le_mul_of_nonneg_left hy (abs_nonneg (conjugate (cutTau^a)))
  have hn : 0 ≤ |conjugate (cutTau^a)| * R := mul_nonneg (abs_nonneg _) hR
  fin_cases j
  · change |conjugate p.1| ≤ (1+|conjugate (cutTau^a)|)*R
    nlinarith
  · change |conjugate p.2| ≤ (1+|conjugate (cutTau^a)|)*R
    nlinarith
  · change |conjugate (p.2-cutTau^a*p.1)| ≤ (1+|conjugate (cutTau^a)|)*R
    rw [map_sub,map_mul]
    calc
      |conjugate p.2-conjugate (cutTau^a)*conjugate p.1| ≤
          |conjugate p.2| + |conjugate (cutTau^a)| * |conjugate p.1| := by
        simpa only [abs_mul] using abs_sub (conjugate p.2) (conjugate (cutTau^a)*conjugate p.1)
      _ ≤ _ := by nlinarith
  · change |conjugate (p.1-cutTau^a*p.2)| ≤ (1+|conjugate (cutTau^a)|)*R
    rw [map_sub,map_mul]
    calc
      |conjugate p.1-conjugate (cutTau^a)*conjugate p.2| ≤
          |conjugate p.1| + |conjugate (cutTau^a)| * |conjugate p.2| := by
        simpa only [abs_mul] using abs_sub (conjugate p.1) (conjugate (cutTau^a)*conjugate p.2)
      _ ≤ _ := by nlinarith

def flagDirectionStrip {a m D : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c ε R : ℝ) :
    Set (FlagSite a m D v) :=
  {z | z∈flagSiteBox R ∧ |cutForm a j z.val.2.val-c| ≤ ε}

theorem flagDirectionStrip_numerators {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) {c ε R : ℝ} (hR : 0 ≤ R) (z : FlagSite a m D v)
    (hz : z∈flagDirectionStrip j c ε R) :
    (cutCoordinates a j (flagSiteNumerator z)).1∈
      cutRectangle (D*(c-ε)) (-(D:ℝ)*(1+|conjugate (cutTau^a)|)*R)
        (2*D*ε) (2*D*(1+|conjugate (cutTau^a)|)*R) ∧
    (cutCoordinates a j (flagSiteNumerator z)).2∈
      cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hb := flagSiteNumerator_box hD z hz.1
  have hx : |conjugate (flagSiteNumerator z).1| ≤ (D:ℝ)*R := by
    exact abs_le.mpr ⟨by linarith [hb.1.2.1],by linarith [hb.1.2.2]⟩
  have hy : |conjugate (flagSiteNumerator z).2| ≤ (D:ℝ)*R := by
    exact abs_le.mpr ⟨by linarith [hb.2.2.1],by linarith [hb.2.2.2]⟩
  have hc := abs_le.mp (cutCoordinates_conjugate_bound a j (flagSiteNumerator z)
    (mul_nonneg hd.le hR) hx hy)
  have he : ordinary (cutCoordinates a j (flagSiteNumerator z)).1 =
      (D:ℝ)*cutForm a j z.val.2.val := by
    rw [cutCoordinates_fst,← cutForm_ordinary,← cutForm_smul]
    congr 1
    have hh := flagSiteNumerator_spec z
    apply Prod.ext
    · have hh₁ := congrArg Prod.fst hh
      change ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 at hh₁
      simpa [smul_eq_mul,mul_comm] using (div_eq_iff hd.ne').mp hh₁
    · have hh₂ := congrArg Prod.snd hh
      change ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 at hh₂
      simpa [smul_eq_mul,mul_comm] using (div_eq_iff hd.ne').mp hh₂
  constructor
  · have hs := abs_le.mp hz.2
    constructor <;> constructor <;> nlinarith [hs.1,hs.2,hc.1,hc.2]
  · fin_cases j <;> first | simpa [cutCoordinates] using hb.1 | simpa [cutCoordinates] using hb.2

theorem flagDirectionStrip_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) {c ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (S : Finset (FlagSite a m D v)) (hS : ∀z∈S,z∈flagDirectionStrip j c ε R) :
    (S.card:ℝ) ≤ m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2)*(2*(D:ℝ)^2*R+2) := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hl : 0 < 1+|conjugate (cutTau^a)| := by positivity
  let T₁ := (cutRectangle_finite (D*(c-ε)) (-(D:ℝ)*(1+|conjugate (cutTau^a)|)*R)
    (2*D*ε) (2*D*(1+|conjugate (cutTau^a)|)*R) (by positivity)).toFinset
  let T₂ := (cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)).toFinset
  have hc₁ : (T₁.card:ℝ) < 4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2 := by
    have hh := cutRectangle_card_bound T₁ _ _ _ _ (by positivity) (by positivity)
      (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    dsimp [T₁] at hh ⊢
    convert hh using 1
    ring
  have hc₂ : (T₂.card:ℝ) < 2*(D:ℝ)^2*R+2 := by
    have hh := cutRectangle_card_bound T₂ 0 (-(D:ℝ)*R) D (2*D*R) hd.le (by positivity)
      (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  let key := fun z : FlagSite a m D v => (z.val.1,cutCoordinates a j (flagSiteNumerator z))
  have hi : Function.Injective key := by
    intro z w h
    have ht : z.val.1=w.val.1 := congrArg (fun x : Fin m × (CutRing×CutRing) => x.1) h
    have hn : cutCoordinates a j (flagSiteNumerator z)=cutCoordinates a j (flagSiteNumerator w) :=
      congrArg (fun x : Fin m × (CutRing×CutRing) => x.2) h
    exact flagSite_key_injective (Prod.ext ht ((cutCoordinates a j).injective hn))
  have hn : S.card ≤ m*T₁.card*T₂.card := by
    rw [← Finset.card_image_of_injective _ hi]
    have hh : S.image key ⊆ (Finset.univ : Finset (Fin m)) ×ˢ (T₁ ×ˢ T₂) := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      have hz' := flagDirectionStrip_numerators hD j hR.le z (hS z hz)
      simpa only [Finset.mem_product,Finset.mem_univ,true_and,key,T₁,T₂,
        Set.Finite.mem_toFinset] using hz'
    simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fin,mul_assoc]
      using Finset.card_le_card hh
  have hn' : (S.card:ℝ) ≤ m*(T₁.card:ℝ)*(T₂.card:ℝ) := by exact_mod_cast hn
  exact hn'.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hc₁.le (Nat.cast_nonneg _)) hc₂.le
    (Nat.cast_nonneg _) (by positivity))

end DirectionStripCounts

section ExceptionalRowCounts
open Classical

theorem flagDirectionStrip_union_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) (T : Finset CutRing) {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,∃c∈T,z∈flagDirectionStrip j (ordinary c) ε R) :
    (S.card:ℝ) ≤ T.card*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2)*
      (2*(D:ℝ)^2*R+2)) := by
  let rows := fun c => S.filter (fun z => z∈flagDirectionStrip j (ordinary c) ε R)
  have hh : S ⊆ T.biUnion rows := by
    intro z hz
    obtain ⟨c,hc,hzc⟩ := hS z hz
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hz,hzc⟩⟩
  have hn : S.card ≤ ∑c∈T,(rows c).card :=
    (Finset.card_le_card hh).trans (Finset.card_biUnion_le)
  have hn' : (S.card:ℝ) ≤ ∑c∈T,((rows c).card:ℝ) := by exact_mod_cast hn
  calc
    (S.card:ℝ) ≤ ∑c∈T,((rows c).card:ℝ) := hn'
    _ ≤ ∑c∈T,(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2)*
        (2*(D:ℝ)^2*R+2)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact flagDirectionStrip_card_bound hD j hε hR (rows c)
        (fun z hz => (Finset.mem_filter.mp hz).2)
    _ = _ := by simp [nsmul_eq_mul]

def boundedCutLevels (A B : ℝ) : Set CutRing :=
  {c | |ordinary c| ≤ A ∧ |conjugate c| ≤ B}

theorem boundedCutLevels_eq (A B : ℝ) :
    boundedCutLevels A B = cutRectangle (-A) (-B) (2*A) (2*B) := by
  ext c
  simp only [boundedCutLevels,cutRectangle,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  constructor <;> rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;> constructor <;> constructor <;> linarith

theorem boundedCutLevels_finite (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (boundedCutLevels A B).Finite := by
  rw [boundedCutLevels_eq]
  exact cutRectangle_finite _ _ _ _ (by positivity)

theorem boundedCutLevels_card_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (T : Finset CutRing) (hT : ∀c∈T,c∈boundedCutLevels A B) :
    (T.card:ℝ) < 4*A*B+2 := by
  have hh := cutRectangle_card_bound T (-A) (-B) (2*A) (2*B) (by positivity)
    (by positivity) (fun c hc => by rw [← boundedCutLevels_eq]; exact hT c hc)
  convert hh using 1
  ring

theorem exceptional_direction_rows {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) {A C Q κ s N : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hQ : 0 < Q)
    (hκ : 0 < κ) (hs : 0 < s) (hN : 1 ≤ N) (hscale : 1 ≤ s*N)
    (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,∃c : CutRing, |ordinary c| ≤ A ∧ |conjugate c| ≤ 2*κ/s ∧
      z∈flagDirectionStrip j (ordinary c) (C*s) (Q*N)) :
    (S.card:ℝ) ≤
      (m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*C*Q+2)*(2*(D:ℝ)^2*Q+2)*(8*A+2))*
        (κ+s)*N^2 := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hN' : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let T := (boundedCutLevels_finite A (show 0 < 2*κ/s by positivity)).toFinset
  have hTc : (T.card:ℝ) ≤ 8*A*κ/s+2 := by
    have hh := boundedCutLevels_card_bound hA (show 0 < 2*κ/s by positivity) T
      (fun c hc => (Set.Finite.mem_toFinset _).mp hc)
    have he : 4*A*(2*κ/s)+2=8*A*κ/s+2 := by ring
    rw [he] at hh
    exact hh.le
  have hTu := flagDirectionStrip_union_card_bound hD j T
    (mul_nonneg hC hs.le) (mul_pos hQ hN') S (by
      intro z hz
      obtain ⟨c,hc₁,hc₂,hzc⟩ := hS z hz
      exact ⟨c,(Set.Finite.mem_toFinset _).mpr ⟨hc₁,hc₂⟩,hzc⟩)
  let U := 4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*C*Q
  let V := 2*(D:ℝ)^2*Q
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have he₁ : 4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(C*s)*(Q*N)+2 ≤ (U+2)*(s*N) := by
    dsimp [U]
    nlinarith
  have he₂ : 2*(D:ℝ)^2*(Q*N)+2 ≤ (V+2)*N := by
    dsimp [V]
    nlinarith
  have hf : 8*A*κ+2*s ≤ (8*A+2)*(κ+s) := by
    nlinarith [mul_nonneg hA hs.le]
  calc
    (S.card:ℝ) ≤ T.card*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(C*s)*(Q*N)+2)*
        (2*(D:ℝ)^2*(Q*N)+2)) := hTu
    _ ≤ (8*A*κ/s+2)*(m*((U+2)*(s*N))*((V+2)*N)) := by
      apply mul_le_mul hTc
      · exact mul_le_mul (mul_le_mul_of_nonneg_left he₁ (Nat.cast_nonneg _)) he₂
          (by positivity) (by positivity)
      · positivity
      · positivity
    _ = (m*(U+2)*(V+2))*(8*A*κ+2*s)*N^2 := by field_simp
    _ ≤ (m*(U+2)*(V+2))*((8*A+2)*(κ+s))*N^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by positivity)) (sq_nonneg N)
    _ = _ := by dsimp [U,V]; ring

end ExceptionalRowCounts

end SimpleAmenable
end
end

end OAI

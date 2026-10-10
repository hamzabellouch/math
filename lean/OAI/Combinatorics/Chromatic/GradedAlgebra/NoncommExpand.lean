import Mathlib

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesDilate
open PowerSeries
noncomputable section
variable {R : Type*} [Semiring R]
variable (w : ℕ) (hw : 0<w)

def dilate (f : PowerSeries R) : PowerSeries R :=
  mk (fun n=>if w∣n then coeff (n/w) f else 0)

@[simp] lemma coeff_dilate (f : PowerSeries R) (n : ℕ) :
    coeff n (dilate w f)=if w∣n then coeff (n/w) f else 0 := by
  rw [dilate,coeff_mk]

lemma dilate_C (r : R) : dilate w (C r)=C r := by
  ext n
  rw [coeff_dilate,coeff_C,coeff_C]
  by_cases hn : n=0
  · subst n; simp
  · rw [ite_eq_right hn]
    by_cases hd : w∣n
    · rw [ite_eq_left hd]
      have H : n/w≠0 := by
        intro hz
        have HE:=Nat.div_mul_cancel hd
        rw [hz,zero_mul] at HE
        exact hn HE.symm
      rw [ite_eq_right H]
    · rw [ite_eq_right hd]

lemma dilate_add (f g : PowerSeries R) : dilate w (f+g)=dilate w f+dilate w g := by
  ext n
  simp only [coeff_dilate,map_add]
  split_ifs <;> simp

def pairEmbedding : ℕ×ℕ ↪ ℕ×ℕ where
  toFun p:=(w*p.1,w*p.2)
  inj':=by
    intro p q h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hw (congrArg Prod.fst h))
      (Nat.eq_of_mul_eq_mul_left hw (congrArg Prod.snd h))

include hw in
lemma dilate_mul (f g : PowerSeries R) : dilate w (f*g)=dilate w f*dilate w g := by
  classical
  ext n
  rw [coeff_dilate,PowerSeries.coeff_mul n]
  by_cases hn : w∣n
  · rw [ite_eq_left hn,PowerSeries.coeff_mul (n/w)]
    let s:=(Finset.HasAntidiagonal.antidiagonal (n/w)).map (pairEmbedding w hw)
    have hs : s⊆Finset.HasAntidiagonal.antidiagonal n := by
      intro p hp
      rcases Finset.mem_map.mp hp with ⟨q,hq,rfl⟩
      have hq' := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      change w*q.1+w*q.2=n
      rw [←Nat.mul_add,hq',Nat.mul_div_cancel' hn]
    calc
      _ = ∑p∈s,coeff p.1 (dilate w f)*coeff p.2 (dilate w g) := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro p hp
        change coeff p.1 f*coeff p.2 g=coeff (w*p.1) (dilate w f)*coeff (w*p.2) (dilate w g)
        simp [hw.ne']
      _ = _ := Finset.sum_subset hs (by
        intro p hp hnot
        rw [coeff_dilate,coeff_dilate]
        by_cases h₁ : w∣p.1
        · have h₂ : ¬w∣p.2 := by
            intro h₂
            apply hnot
            apply Finset.mem_map.mpr
            refine ⟨(p.1/w,p.2/w),?_,?_⟩
            · rw [Finset.HasAntidiagonal.mem_antidiagonal]
              have HH:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
              rw [←Nat.add_div_of_dvd_left h₂,HH]
            · change (w*(p.1/w),w*(p.2/w))=p
              rw [Nat.mul_div_cancel' h₁,Nat.mul_div_cancel' h₂]
          simp [h₂]
        · simp [h₁])
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    rw [coeff_dilate,coeff_dilate]
    by_cases h₁ : w∣p.1
    · have h₂ : ¬w∣p.2 := by
        intro h₂
        exact hn (Finset.HasAntidiagonal.mem_antidiagonal.mp hp ▸ dvd_add h₁ h₂)
      simp [h₂]
    · simp [h₁]

def hom : PowerSeries R →+* PowerSeries R where
  toFun:=dilate w
  map_one':=by simpa only [map_one] using dilate_C w (R:=R) 1
  map_zero':=by simpa only [map_zero] using dilate_C w (R:=R) 0
  map_add':=dilate_add w
  map_mul':=dilate_mul w hw
end
end ElementaryPositivity.PowerSeriesDilate

end

end OAI

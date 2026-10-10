import OAI.Algebra.OddKaplansky.HeisenbergRepresentation

namespace OAI

universe portUniverse1

section
namespace OddKaplansky.Heisenberg
noncomputable section
open scoped Classical BigOperators Matrix
variable (M q : ℕ) [NeZero M] {K : Type portUniverse1} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
variable (hc : (Fintype.card (Fourier.C M) : K) ≠ 0) (hz : (Fintype.card (Z M q) : K) ≠ 0)
abbrev Sector := LinearMap.range (Algebra.lmul K (MonoidAlgebra K (GroupData M q)) (f M q hζ))
lemma mem_sector_of_fixed {a : MonoidAlgebra K (GroupData M q)} (ha : f M q hζ*a=a) : a ∈ Sector M q hζ := ⟨a,ha⟩
include hc in
lemma fixed_of_mem_sector {a : MonoidAlgebra K (GroupData M q)} (ha : a ∈ Sector M q hζ) : f M q hζ*a=a := by
  obtain ⟨a,rfl⟩ := ha
  change f M q hζ*(f M q hζ*a)=f M q hζ*a
  rw [← mul_assoc,f_idempotent M q hζ hc]
include hc in
lemma Ω_fixed (u v : Z M q) : f M q hζ*Ω M q hζ u v=Ω M q hζ u v := by
  unfold Ω D
  rw [← mul_assoc,(f_central M q hζ _).eq,mul_assoc,← mul_assoc (f M q hζ),f_idempotent M q hζ hc]
def frame (xy : Z M q × Z M q) : MonoidAlgebra K (GroupData M q) := f M q hζ * MonoidAlgebra.single ⟨xy.1,xy.2,1⟩ 1
lemma f_single (g : GroupData M q) : f M q hζ*MonoidAlgebra.single g 1 = (Fourier.cyclicCharacter M hζ g.k : K) • frame M q hζ (g.x,g.y) := by
  have hg : central M q g.k * (⟨g.x,g.y,1⟩ : GroupData M q)=g := by ext <;> simp [central,dot_one_left]
  have hs : MonoidAlgebra.single g (1 : K)=MonoidAlgebra.single (central M q g.k) 1*MonoidAlgebra.single (⟨g.x,g.y,1⟩ : GroupData M q) 1 := by rw [MonoidAlgebra.single_mul_single,one_mul,hg]
  rw [hs,← mul_assoc]
  have hh := CharacterIdempotents.pushed_mul_single (central M q) (Fourier.cyclicCharacter M hζ) g.k
  change f M q hζ*MonoidAlgebra.single (central M q g.k) 1=(Fourier.cyclicCharacter M hζ g.k : K) • f M q hζ at hh
  rw [hh,smul_mul_assoc]
  rfl
lemma span_frame : Submodule.span K (Set.range (frame M q hζ))=Sector M q hζ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨xy,rfl⟩
    exact ⟨_,rfl⟩
  · rintro _ ⟨a,rfl⟩
    change f M q hζ*a ∈ _
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.of_apply,f_single]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g.x,g.y),rfl⟩)
    | add a b ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
lemma sector_dim_le : Module.finrank K (Sector M q hζ) ≤ Fintype.card (Z M q)*Fintype.card (Z M q) := by
  rw [← span_frame]
  simpa only [Set.finrank,Fintype.card_prod] using finrank_range_le_card (R := K) (frame M q hζ)

def encode : Matrix (Z M q) (Z M q) K →ₗ[K] MonoidAlgebra K (GroupData M q) where
  toFun T := ∑ u,∑ v,T u v • Ω M q hζ u v
  map_add' T S := by simp only [Matrix.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c T := by simp only [Matrix.smul_apply,smul_smul,smul_eq_mul,Finset.smul_sum,RingHom.id_apply]
lemma encode_apply (T : Matrix (Z M q) (Z M q) K) : encode M q hζ T=∑ u,∑ v,T u v • Ω M q hζ u v := rfl
include hc in
lemma encode_fixed (T : Matrix (Z M q) (Z M q) K) : f M q hζ*encode M q hζ T = encode M q hζ T := by
  simp only [encode_apply,Finset.mul_sum,mul_smul_comm,Ω_fixed M q hζ hc]
include hc hz in
lemma ρ_encode (T : Matrix (Z M q) (Z M q) K) : ρ M q hζ (encode M q hζ T)=T := by
  simp only [encode_apply,map_sum,map_smul,ρ_Ω M q hζ hc hz]
  ext u v
  simp [Matrix.sum_apply,Matrix.single_apply,ite_and]
include hc hz in
lemma encode_injective : Function.Injective (encode M q hζ) := by
  intro T S he
  have hh := congrArg (ρ M q hζ) he
  simpa only [ρ_encode M q hζ hc hz] using hh
include hc hz in
lemma encode_range : LinearMap.range (encode M q hζ)=Sector M q hζ := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨T,rfl⟩
    exact mem_sector_of_fixed _ _ _ (encode_fixed M q hζ hc T)
  · rw [LinearMap.finrank_range_of_inj (encode_injective M q hζ hc hz)]
    simpa only [Module.finrank_matrix,Module.finrank_self,mul_one] using sector_dim_le M q hζ
include hc hz in
lemma ρ_injective_on_sector {a b : MonoidAlgebra K (GroupData M q)}
    (ha : a ∈ Sector M q hζ) (hb : b ∈ Sector M q hζ) (he : ρ M q hζ a=ρ M q hζ b) : a=b := by
  rw [← encode_range M q hζ hc hz] at ha hb
  obtain ⟨T,rfl⟩ := ha
  obtain ⟨S,rfl⟩ := hb
  rw [ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz] at he
  rw [he]
include hc hz in
lemma Ω_mul (u v s t : Z M q) : Ω M q hζ u v*Ω M q hζ s t=if v=s then Ω M q hζ u t else 0 := by
  apply ρ_injective_on_sector M q hζ hc hz
  · apply mem_sector_of_fixed
    rw [← mul_assoc,Ω_fixed M q hζ hc]
  · split_ifs
    · exact mem_sector_of_fixed _ _ _ (Ω_fixed M q hζ hc _ _)
    · exact Submodule.zero_mem _
  · rw [map_mul,ρ_Ω M q hζ hc hz,ρ_Ω M q hζ hc hz]
    split_ifs with hv <;> simp only [ρ_Ω M q hζ hc hz,map_zero]
    all_goals
      ext a b
      simp [Matrix.mul_apply,Matrix.single_apply,ite_and,mul_ite,hv] <;> split_ifs <;> rfl
include hc hz in
lemma Ω_sum : ∑ u : Z M q, Ω M q hζ u u=f M q hζ := by
  apply ρ_injective_on_sector M q hζ hc hz
  · apply mem_sector_of_fixed
    simp only [Finset.mul_sum,Ω_fixed M q hζ hc]
  · exact ⟨1,by simp⟩
  · rw [map_sum,ρ_f M q hζ hc]
    simp only [ρ_Ω M q hζ hc hz]
    ext a b
    simp [Matrix.sum_apply,Matrix.single_apply,Matrix.one_apply,ite_and,eq_comm]
include hc hz in
lemma Ω_ne_zero (u v : Z M q) : Ω M q hζ u v≠0 := by
  intro he
  have hh := congrArg (fun a => ρ M q hζ a u v) he
  rw [ρ_Ω M q hζ hc hz,map_zero] at hh
  simp at hh
include hc hz in
lemma encode_mul (T S : Matrix (Z M q) (Z M q) K) : encode M q hζ (T*S)=encode M q hζ T*encode M q hζ S := by
  apply ρ_injective_on_sector M q hζ hc hz
  · exact mem_sector_of_fixed _ _ _ (encode_fixed M q hζ hc _)
  · apply mem_sector_of_fixed
    rw [← mul_assoc,encode_fixed M q hζ hc]
  · have hh : ρ M q hζ (encode M q hζ T*encode M q hζ S)=ρ M q hζ (encode M q hζ T)*ρ M q hζ (encode M q hζ S) := map_mul (ρ M q hζ) _ _
    rw [hh,ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz,ρ_encode M q hζ hc hz]
end
end OddKaplansky.Heisenberg

end

end OAI

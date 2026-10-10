import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates070
import OAI.Combinatorics.Ramsey.CycleClique.Certificates071
import OAI.Combinatorics.Ramsey.CycleClique.Certificates072
import OAI.Combinatorics.Ramsey.CycleClique.Certificates073
import OAI.Combinatorics.Ramsey.CycleClique.Certificates074
import OAI.Combinatorics.Ramsey.CycleClique.Certificates075
import OAI.Combinatorics.Ramsey.CycleClique.Certificates076
import OAI.Combinatorics.Ramsey.CycleClique.Certificates077
import OAI.Combinatorics.Ramsey.CycleClique.Certificates078
import OAI.Combinatorics.Ramsey.CycleClique.Certificates079
import OAI.Combinatorics.Ramsey.CycleClique.Certificates080
import OAI.Combinatorics.Ramsey.CycleClique.Certificates081
import OAI.Combinatorics.Ramsey.CycleClique.Certificates082
import OAI.Combinatorics.Ramsey.CycleClique.Certificates083
import OAI.Combinatorics.Ramsey.CycleClique.Certificates084
import OAI.Combinatorics.Ramsey.CycleClique.Certificates085
import OAI.Combinatorics.Ramsey.CycleClique.Certificates086
import OAI.Combinatorics.Ramsey.CycleClique.Certificates087
import OAI.Combinatorics.Ramsey.CycleClique.Certificates088
import OAI.Combinatorics.Ramsey.CycleClique.Certificates089
import OAI.Combinatorics.Ramsey.CycleClique.Certificates090
import OAI.Combinatorics.Ramsey.CycleClique.Certificates091
import OAI.Combinatorics.Ramsey.CycleClique.Certificates092
import OAI.Combinatorics.Ramsey.CycleClique.Certificates093
import OAI.Combinatorics.Ramsey.CycleClique.Certificates094
import OAI.Combinatorics.Ramsey.CycleClique.Certificates095
import OAI.Combinatorics.Ramsey.CycleClique.Certificates096
import OAI.Combinatorics.Ramsey.CycleClique.Certificates097
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_17_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[],[7]],[[],[],[],[],[],[],[8]],[[],[],[],[],[],[],[9]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[1,6]]]

theorem patterns_17_8_0_verified : ∀ D ∈ patterns_17_8_0, PatternVerified 17 8 D := by

  simp only [patterns_17_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_2220, certificate_2220_valid⟩, ⟨⟨certificate_2221, certificate_2221_valid⟩, ⟨⟨certificate_2222, certificate_2222_valid⟩, ⟨⟨certificate_2223, certificate_2223_valid⟩, ⟨⟨certificate_2224, certificate_2224_valid⟩, ⟨⟨certificate_2225, certificate_2225_valid⟩, ⟨⟨certificate_2226, certificate_2226_valid⟩, ⟨⟨certificate_2227, certificate_2227_valid⟩, ⟨⟨certificate_2228, certificate_2228_valid⟩, ⟨⟨certificate_2229, certificate_2229_valid⟩, ⟨⟨certificate_2230, certificate_2230_valid⟩, ⟨⟨certificate_2231, certificate_2231_valid⟩, ⟨⟨certificate_2232, certificate_2232_valid⟩, ⟨⟨certificate_2233, certificate_2233_valid⟩, ⟨⟨certificate_2234, certificate_2234_valid⟩, ⟨⟨certificate_2235, certificate_2235_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_1 : List (List (List ℕ)) := [[[],[],[],[],[],[1,7]],[[],[],[],[],[],[1,8]],[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[],[2,4]],[[],[],[],[],[],[2,5]],[[],[],[],[],[],[2,6]],[[],[],[],[],[],[2,7]],[[],[],[],[],[],[3,3]],[[],[],[],[],[],[3,4]],[[],[],[],[],[],[3,5]],[[],[],[],[],[],[3,6]],[[],[],[],[],[],[4,4]],[[],[],[],[],[],[4,5]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]]]

theorem patterns_17_8_1_verified : ∀ D ∈ patterns_17_8_1, PatternVerified 17 8 D := by

  simp only [patterns_17_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_2236, certificate_2236_valid⟩, ⟨⟨certificate_2237, certificate_2237_valid⟩, ⟨⟨certificate_2238, certificate_2238_valid⟩, ⟨⟨certificate_2239, certificate_2239_valid⟩, ⟨⟨certificate_2240, certificate_2240_valid⟩, ⟨⟨certificate_2241, certificate_2241_valid⟩, ⟨⟨certificate_2242, certificate_2242_valid⟩, ⟨⟨certificate_2243, certificate_2243_valid⟩, ⟨⟨certificate_2244, certificate_2244_valid⟩, ⟨⟨certificate_2245, certificate_2245_valid⟩, ⟨⟨certificate_2246, certificate_2246_valid⟩, ⟨⟨certificate_2247, certificate_2247_valid⟩, ⟨⟨certificate_2248, certificate_2248_valid⟩, ⟨⟨certificate_2249, certificate_2249_valid⟩, ⟨⟨certificate_2250, certificate_2250_valid⟩, ⟨⟨certificate_2251, certificate_2251_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_2 : List (List (List ℕ)) := [[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1],[6]],[[],[],[],[],[1],[7]],[[],[],[],[],[1],[8]],[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,1,5]],[[],[],[],[],[1,1,6]],[[],[],[],[],[1,1,7]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]]]

theorem patterns_17_8_2_verified : ∀ D ∈ patterns_17_8_2, PatternVerified 17 8 D := by

  simp only [patterns_17_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_2252, certificate_2252_valid⟩, ⟨⟨certificate_2253, certificate_2253_valid⟩, ⟨⟨certificate_2254, certificate_2254_valid⟩, ⟨⟨certificate_2255, certificate_2255_valid⟩, ⟨⟨certificate_2256, certificate_2256_valid⟩, ⟨⟨certificate_2257, certificate_2257_valid⟩, ⟨⟨certificate_2258, certificate_2258_valid⟩, ⟨⟨certificate_2259, certificate_2259_valid⟩, ⟨⟨certificate_2260, certificate_2260_valid⟩, ⟨⟨certificate_2261, certificate_2261_valid⟩, ⟨⟨certificate_2262, certificate_2262_valid⟩, ⟨⟨certificate_2263, certificate_2263_valid⟩, ⟨⟨certificate_2264, certificate_2264_valid⟩, ⟨⟨certificate_2265, certificate_2265_valid⟩, ⟨⟨certificate_2266, certificate_2266_valid⟩, ⟨⟨certificate_2267, certificate_2267_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_3 : List (List (List ℕ)) := [[[],[],[],[],[1,2,4]],[[],[],[],[],[1,2,5]],[[],[],[],[],[1,2,6]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,3,3]],[[],[],[],[],[1,3,4]],[[],[],[],[],[1,3,5]],[[],[],[],[],[1,4,1]],[[],[],[],[],[1,4,2]],[[],[],[],[],[1,4,3]],[[],[],[],[],[1,4,4]],[[],[],[],[],[1,5,1]],[[],[],[],[],[1,5,2]],[[],[],[],[],[1,5,3]],[[],[],[],[],[1,6,1]]]

theorem patterns_17_8_3_verified : ∀ D ∈ patterns_17_8_3, PatternVerified 17 8 D := by

  simp only [patterns_17_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_2268, certificate_2268_valid⟩, ⟨⟨certificate_2269, certificate_2269_valid⟩, ⟨⟨certificate_2270, certificate_2270_valid⟩, ⟨⟨certificate_2271, certificate_2271_valid⟩, ⟨⟨certificate_2272, certificate_2272_valid⟩, ⟨⟨certificate_2273, certificate_2273_valid⟩, ⟨⟨certificate_2274, certificate_2274_valid⟩, ⟨⟨certificate_2275, certificate_2275_valid⟩, ⟨⟨certificate_2276, certificate_2276_valid⟩, ⟨⟨certificate_2277, certificate_2277_valid⟩, ⟨⟨certificate_2278, certificate_2278_valid⟩, ⟨⟨certificate_2279, certificate_2279_valid⟩, ⟨⟨certificate_2280, certificate_2280_valid⟩, ⟨⟨certificate_2281, certificate_2281_valid⟩, ⟨⟨certificate_2282, certificate_2282_valid⟩, ⟨⟨certificate_2283, certificate_2283_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_4 : List (List (List ℕ)) := [[[],[],[],[],[1,6,2]],[[],[],[],[],[1,7,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2],[5]],[[],[],[],[],[2],[6]],[[],[],[],[],[2],[7]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,1,4]],[[],[],[],[],[2,1,5]],[[],[],[],[],[2,1,6]],[[],[],[],[],[2,2,2]],[[],[],[],[],[2,2,3]],[[],[],[],[],[2,2,4]]]

theorem patterns_17_8_4_verified : ∀ D ∈ patterns_17_8_4, PatternVerified 17 8 D := by

  simp only [patterns_17_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_2284, certificate_2284_valid⟩, ⟨⟨certificate_2285, certificate_2285_valid⟩, ⟨⟨certificate_2286, certificate_2286_valid⟩, ⟨⟨certificate_2287, certificate_2287_valid⟩, ⟨⟨certificate_2288, certificate_2288_valid⟩, ⟨⟨certificate_2289, certificate_2289_valid⟩, ⟨⟨certificate_2290, certificate_2290_valid⟩, ⟨⟨certificate_2291, certificate_2291_valid⟩, ⟨⟨certificate_2292, certificate_2292_valid⟩, ⟨⟨certificate_2293, certificate_2293_valid⟩, ⟨⟨certificate_2294, certificate_2294_valid⟩, ⟨⟨certificate_2295, certificate_2295_valid⟩, ⟨⟨certificate_2296, certificate_2296_valid⟩, ⟨⟨certificate_2297, certificate_2297_valid⟩, ⟨⟨certificate_2298, certificate_2298_valid⟩, ⟨⟨certificate_2299, certificate_2299_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_5 : List (List (List ℕ)) := [[[],[],[],[],[2,2,5]],[[],[],[],[],[2,3,2]],[[],[],[],[],[2,3,3]],[[],[],[],[],[2,3,4]],[[],[],[],[],[2,4,2]],[[],[],[],[],[2,4,3]],[[],[],[],[],[2,5,2]],[[],[],[],[],[3],[3]],[[],[],[],[],[3],[4]],[[],[],[],[],[3],[5]],[[],[],[],[],[3],[6]],[[],[],[],[],[3,1,3]],[[],[],[],[],[3,1,4]],[[],[],[],[],[3,1,5]],[[],[],[],[],[3,2,3]],[[],[],[],[],[3,2,4]]]

theorem patterns_17_8_5_verified : ∀ D ∈ patterns_17_8_5, PatternVerified 17 8 D := by

  simp only [patterns_17_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_2300, certificate_2300_valid⟩, ⟨⟨certificate_2301, certificate_2301_valid⟩, ⟨⟨certificate_2302, certificate_2302_valid⟩, ⟨⟨certificate_2303, certificate_2303_valid⟩, ⟨⟨certificate_2304, certificate_2304_valid⟩, ⟨⟨certificate_2305, certificate_2305_valid⟩, ⟨⟨certificate_2306, certificate_2306_valid⟩, ⟨⟨certificate_2307, certificate_2307_valid⟩, ⟨⟨certificate_2308, certificate_2308_valid⟩, ⟨⟨certificate_2309, certificate_2309_valid⟩, ⟨⟨certificate_2310, certificate_2310_valid⟩, ⟨⟨certificate_2311, certificate_2311_valid⟩, ⟨⟨certificate_2312, certificate_2312_valid⟩, ⟨⟨certificate_2313, certificate_2313_valid⟩, ⟨⟨certificate_2314, certificate_2314_valid⟩, ⟨⟨certificate_2315, certificate_2315_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_6 : List (List (List ℕ)) := [[[],[],[],[],[3,3,3]],[[],[],[],[],[4],[4]],[[],[],[],[],[4],[5]],[[],[],[],[],[4,1,4]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[1,5]],[[],[],[],[1],[1,6]],[[],[],[],[1],[1,7]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1],[2,4]],[[],[],[],[1],[2,5]],[[],[],[],[1],[2,6]]]

theorem patterns_17_8_6_verified : ∀ D ∈ patterns_17_8_6, PatternVerified 17 8 D := by

  simp only [patterns_17_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_2316, certificate_2316_valid⟩, ⟨⟨certificate_2317, certificate_2317_valid⟩, ⟨⟨certificate_2318, certificate_2318_valid⟩, ⟨⟨certificate_2319, certificate_2319_valid⟩, ⟨⟨certificate_2320, certificate_2320_valid⟩, ⟨⟨certificate_2321, certificate_2321_valid⟩, ⟨⟨certificate_2322, certificate_2322_valid⟩, ⟨⟨certificate_2323, certificate_2323_valid⟩, ⟨⟨certificate_2324, certificate_2324_valid⟩, ⟨⟨certificate_2325, certificate_2325_valid⟩, ⟨⟨certificate_2326, certificate_2326_valid⟩, ⟨⟨certificate_2327, certificate_2327_valid⟩, ⟨⟨certificate_2328, certificate_2328_valid⟩, ⟨⟨certificate_2329, certificate_2329_valid⟩, ⟨⟨certificate_2330, certificate_2330_valid⟩, ⟨⟨certificate_2331, certificate_2331_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_7 : List (List (List ℕ)) := [[[],[],[],[1],[3,3]],[[],[],[],[1],[3,4]],[[],[],[],[1],[3,5]],[[],[],[],[1],[4,4]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1],[5]],[[],[],[],[1,1],[6]],[[],[],[],[1,1],[7]],[[],[],[],[1,1,1,1]],[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,1,4]],[[],[],[],[1,1,1,5]],[[],[],[],[1,1,1,6]]]

theorem patterns_17_8_7_verified : ∀ D ∈ patterns_17_8_7, PatternVerified 17 8 D := by

  simp only [patterns_17_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_2332, certificate_2332_valid⟩, ⟨⟨certificate_2333, certificate_2333_valid⟩, ⟨⟨certificate_2334, certificate_2334_valid⟩, ⟨⟨certificate_2335, certificate_2335_valid⟩, ⟨⟨certificate_2336, certificate_2336_valid⟩, ⟨⟨certificate_2337, certificate_2337_valid⟩, ⟨⟨certificate_2338, certificate_2338_valid⟩, ⟨⟨certificate_2339, certificate_2339_valid⟩, ⟨⟨certificate_2340, certificate_2340_valid⟩, ⟨⟨certificate_2341, certificate_2341_valid⟩, ⟨⟨certificate_2342, certificate_2342_valid⟩, ⟨⟨certificate_2343, certificate_2343_valid⟩, ⟨⟨certificate_2344, certificate_2344_valid⟩, ⟨⟨certificate_2345, certificate_2345_valid⟩, ⟨⟨certificate_2346, certificate_2346_valid⟩, ⟨⟨certificate_2347, certificate_2347_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_8 : List (List (List ℕ)) := [[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,2,3]],[[],[],[],[1,1,2,4]],[[],[],[],[1,1,2,5]],[[],[],[],[1,1,3,1]],[[],[],[],[1,1,3,2]],[[],[],[],[1,1,3,3]],[[],[],[],[1,1,3,4]],[[],[],[],[1,1,4,1]],[[],[],[],[1,1,4,2]],[[],[],[],[1,1,4,3]],[[],[],[],[1,1,5,1]],[[],[],[],[1,1,5,2]],[[],[],[],[1,1,6,1]],[[],[],[],[1,2],[2]]]

theorem patterns_17_8_8_verified : ∀ D ∈ patterns_17_8_8, PatternVerified 17 8 D := by

  simp only [patterns_17_8_8, List.forall_mem_cons]

  exact ⟨⟨certificate_2348, certificate_2348_valid⟩, ⟨⟨certificate_2349, certificate_2349_valid⟩, ⟨⟨certificate_2350, certificate_2350_valid⟩, ⟨⟨certificate_2351, certificate_2351_valid⟩, ⟨⟨certificate_2352, certificate_2352_valid⟩, ⟨⟨certificate_2353, certificate_2353_valid⟩, ⟨⟨certificate_2354, certificate_2354_valid⟩, ⟨⟨certificate_2355, certificate_2355_valid⟩, ⟨⟨certificate_2356, certificate_2356_valid⟩, ⟨⟨certificate_2357, certificate_2357_valid⟩, ⟨⟨certificate_2358, certificate_2358_valid⟩, ⟨⟨certificate_2359, certificate_2359_valid⟩, ⟨⟨certificate_2360, certificate_2360_valid⟩, ⟨⟨certificate_2361, certificate_2361_valid⟩, ⟨⟨certificate_2362, certificate_2362_valid⟩, ⟨⟨certificate_2363, certificate_2363_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_9 : List (List (List ℕ)) := [[[],[],[],[1,2],[3]],[[],[],[],[1,2],[4]],[[],[],[],[1,2],[5]],[[],[],[],[1,2],[6]],[[],[],[],[1,2,1,2]],[[],[],[],[1,2,1,3]],[[],[],[],[1,2,1,4]],[[],[],[],[1,2,1,5]],[[],[],[],[1,2,2,1]],[[],[],[],[1,2,2,2]],[[],[],[],[1,2,2,3]],[[],[],[],[1,2,2,4]],[[],[],[],[1,2,3,1]],[[],[],[],[1,2,3,2]],[[],[],[],[1,2,3,3]],[[],[],[],[1,2,4,1]]]

theorem patterns_17_8_9_verified : ∀ D ∈ patterns_17_8_9, PatternVerified 17 8 D := by

  simp only [patterns_17_8_9, List.forall_mem_cons]

  exact ⟨⟨certificate_2364, certificate_2364_valid⟩, ⟨⟨certificate_2365, certificate_2365_valid⟩, ⟨⟨certificate_2366, certificate_2366_valid⟩, ⟨⟨certificate_2367, certificate_2367_valid⟩, ⟨⟨certificate_2368, certificate_2368_valid⟩, ⟨⟨certificate_2369, certificate_2369_valid⟩, ⟨⟨certificate_2370, certificate_2370_valid⟩, ⟨⟨certificate_2371, certificate_2371_valid⟩, ⟨⟨certificate_2372, certificate_2372_valid⟩, ⟨⟨certificate_2373, certificate_2373_valid⟩, ⟨⟨certificate_2374, certificate_2374_valid⟩, ⟨⟨certificate_2375, certificate_2375_valid⟩, ⟨⟨certificate_2376, certificate_2376_valid⟩, ⟨⟨certificate_2377, certificate_2377_valid⟩, ⟨⟨certificate_2378, certificate_2378_valid⟩, ⟨⟨certificate_2379, certificate_2379_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_10 : List (List (List ℕ)) := [[[],[],[],[1,2,4,2]],[[],[],[],[1,2,5,1]],[[],[],[],[1,3],[2]],[[],[],[],[1,3],[3]],[[],[],[],[1,3],[4]],[[],[],[],[1,3],[5]],[[],[],[],[1,3,1,2]],[[],[],[],[1,3,1,3]],[[],[],[],[1,3,1,4]],[[],[],[],[1,3,2,2]],[[],[],[],[1,3,2,3]],[[],[],[],[1,3,3,1]],[[],[],[],[1,3,3,2]],[[],[],[],[1,3,4,1]],[[],[],[],[1,4],[2]],[[],[],[],[1,4],[3]]]

theorem patterns_17_8_10_verified : ∀ D ∈ patterns_17_8_10, PatternVerified 17 8 D := by

  simp only [patterns_17_8_10, List.forall_mem_cons]

  exact ⟨⟨certificate_2380, certificate_2380_valid⟩, ⟨⟨certificate_2381, certificate_2381_valid⟩, ⟨⟨certificate_2382, certificate_2382_valid⟩, ⟨⟨certificate_2383, certificate_2383_valid⟩, ⟨⟨certificate_2384, certificate_2384_valid⟩, ⟨⟨certificate_2385, certificate_2385_valid⟩, ⟨⟨certificate_2386, certificate_2386_valid⟩, ⟨⟨certificate_2387, certificate_2387_valid⟩, ⟨⟨certificate_2388, certificate_2388_valid⟩, ⟨⟨certificate_2389, certificate_2389_valid⟩, ⟨⟨certificate_2390, certificate_2390_valid⟩, ⟨⟨certificate_2391, certificate_2391_valid⟩, ⟨⟨certificate_2392, certificate_2392_valid⟩, ⟨⟨certificate_2393, certificate_2393_valid⟩, ⟨⟨certificate_2394, certificate_2394_valid⟩, ⟨⟨certificate_2395, certificate_2395_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_11 : List (List (List ℕ)) := [[[],[],[],[1,4],[4]],[[],[],[],[1,4,1,2]],[[],[],[],[1,4,1,3]],[[],[],[],[1,4,2,2]],[[],[],[],[1,5],[2]],[[],[],[],[1,5],[3]],[[],[],[],[1,5,1,2]],[[],[],[],[1,6],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2],[2,3]],[[],[],[],[2],[2,4]],[[],[],[],[2],[2,5]],[[],[],[],[2],[3,3]],[[],[],[],[2],[3,4]],[[],[],[],[2,1,1,2]],[[],[],[],[2,1,1,3]]]

theorem patterns_17_8_11_verified : ∀ D ∈ patterns_17_8_11, PatternVerified 17 8 D := by

  simp only [patterns_17_8_11, List.forall_mem_cons]

  exact ⟨⟨certificate_2396, certificate_2396_valid⟩, ⟨⟨certificate_2397, certificate_2397_valid⟩, ⟨⟨certificate_2398, certificate_2398_valid⟩, ⟨⟨certificate_2399, certificate_2399_valid⟩, ⟨⟨certificate_2400, certificate_2400_valid⟩, ⟨⟨certificate_2401, certificate_2401_valid⟩, ⟨⟨certificate_2402, certificate_2402_valid⟩, ⟨⟨certificate_2403, certificate_2403_valid⟩, ⟨⟨certificate_2404, certificate_2404_valid⟩, ⟨⟨certificate_2405, certificate_2405_valid⟩, ⟨⟨certificate_2406, certificate_2406_valid⟩, ⟨⟨certificate_2407, certificate_2407_valid⟩, ⟨⟨certificate_2408, certificate_2408_valid⟩, ⟨⟨certificate_2409, certificate_2409_valid⟩, ⟨⟨certificate_2410, certificate_2410_valid⟩, ⟨⟨certificate_2411, certificate_2411_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_12 : List (List (List ℕ)) := [[[],[],[],[2,1,1,4]],[[],[],[],[2,1,1,5]],[[],[],[],[2,1,2,2]],[[],[],[],[2,1,2,3]],[[],[],[],[2,1,2,4]],[[],[],[],[2,1,3,2]],[[],[],[],[2,1,3,3]],[[],[],[],[2,1,4,2]],[[],[],[],[2,2],[3]],[[],[],[],[2,2],[4]],[[],[],[],[2,2],[5]],[[],[],[],[2,2,1,3]],[[],[],[],[2,2,1,4]],[[],[],[],[2,2,2,2]],[[],[],[],[2,2,2,3]],[[],[],[],[2,2,3,2]]]

theorem patterns_17_8_12_verified : ∀ D ∈ patterns_17_8_12, PatternVerified 17 8 D := by

  simp only [patterns_17_8_12, List.forall_mem_cons]

  exact ⟨⟨certificate_2412, certificate_2412_valid⟩, ⟨⟨certificate_2413, certificate_2413_valid⟩, ⟨⟨certificate_2414, certificate_2414_valid⟩, ⟨⟨certificate_2415, certificate_2415_valid⟩, ⟨⟨certificate_2416, certificate_2416_valid⟩, ⟨⟨certificate_2417, certificate_2417_valid⟩, ⟨⟨certificate_2418, certificate_2418_valid⟩, ⟨⟨certificate_2419, certificate_2419_valid⟩, ⟨⟨certificate_2420, certificate_2420_valid⟩, ⟨⟨certificate_2421, certificate_2421_valid⟩, ⟨⟨certificate_2422, certificate_2422_valid⟩, ⟨⟨certificate_2423, certificate_2423_valid⟩, ⟨⟨certificate_2424, certificate_2424_valid⟩, ⟨⟨certificate_2425, certificate_2425_valid⟩, ⟨⟨certificate_2426, certificate_2426_valid⟩, ⟨⟨certificate_2427, certificate_2427_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_13 : List (List (List ℕ)) := [[[],[],[],[2,3],[3]],[[],[],[],[2,3],[4]],[[],[],[],[2,3,1,3]],[[],[],[],[2,4],[3]],[[],[],[],[3],[3,3]],[[],[],[],[3,1,1,3]],[[],[],[],[3,1,1,4]],[[],[],[],[3,1,2,3]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]],[[],[],[1],[1],[5]],[[],[],[1],[1],[6]],[[],[],[1],[1],[7]],[[],[],[1],[1,1,1]]]

theorem patterns_17_8_13_verified : ∀ D ∈ patterns_17_8_13, PatternVerified 17 8 D := by

  simp only [patterns_17_8_13, List.forall_mem_cons]

  exact ⟨⟨certificate_2428, certificate_2428_valid⟩, ⟨⟨certificate_2429, certificate_2429_valid⟩, ⟨⟨certificate_2430, certificate_2430_valid⟩, ⟨⟨certificate_2431, certificate_2431_valid⟩, ⟨⟨certificate_2432, certificate_2432_valid⟩, ⟨⟨certificate_2433, certificate_2433_valid⟩, ⟨⟨certificate_2434, certificate_2434_valid⟩, ⟨⟨certificate_2435, certificate_2435_valid⟩, ⟨⟨certificate_2436, certificate_2436_valid⟩, ⟨⟨certificate_2437, certificate_2437_valid⟩, ⟨⟨certificate_2438, certificate_2438_valid⟩, ⟨⟨certificate_2439, certificate_2439_valid⟩, ⟨⟨certificate_2440, certificate_2440_valid⟩, ⟨⟨certificate_2441, certificate_2441_valid⟩, ⟨⟨certificate_2442, certificate_2442_valid⟩, ⟨⟨certificate_2443, certificate_2443_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_14 : List (List (List ℕ)) := [[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,1,4]],[[],[],[1],[1,1,5]],[[],[],[1],[1,1,6]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]],[[],[],[1],[1,2,3]],[[],[],[1],[1,2,4]],[[],[],[1],[1,2,5]],[[],[],[1],[1,3,1]],[[],[],[1],[1,3,2]],[[],[],[1],[1,3,3]],[[],[],[1],[1,3,4]],[[],[],[1],[1,4,1]],[[],[],[1],[1,4,2]]]

theorem patterns_17_8_14_verified : ∀ D ∈ patterns_17_8_14, PatternVerified 17 8 D := by

  simp only [patterns_17_8_14, List.forall_mem_cons]

  exact ⟨⟨certificate_2444, certificate_2444_valid⟩, ⟨⟨certificate_2445, certificate_2445_valid⟩, ⟨⟨certificate_2446, certificate_2446_valid⟩, ⟨⟨certificate_2447, certificate_2447_valid⟩, ⟨⟨certificate_2448, certificate_2448_valid⟩, ⟨⟨certificate_2449, certificate_2449_valid⟩, ⟨⟨certificate_2450, certificate_2450_valid⟩, ⟨⟨certificate_2451, certificate_2451_valid⟩, ⟨⟨certificate_2452, certificate_2452_valid⟩, ⟨⟨certificate_2453, certificate_2453_valid⟩, ⟨⟨certificate_2454, certificate_2454_valid⟩, ⟨⟨certificate_2455, certificate_2455_valid⟩, ⟨⟨certificate_2456, certificate_2456_valid⟩, ⟨⟨certificate_2457, certificate_2457_valid⟩, ⟨⟨certificate_2458, certificate_2458_valid⟩, ⟨⟨certificate_2459, certificate_2459_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_15 : List (List (List ℕ)) := [[[],[],[1],[1,4,3]],[[],[],[1],[1,5,1]],[[],[],[1],[1,5,2]],[[],[],[1],[1,6,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]],[[],[],[1],[2],[4]],[[],[],[1],[2],[5]],[[],[],[1],[2],[6]],[[],[],[1],[2,1,2]],[[],[],[1],[2,1,3]],[[],[],[1],[2,1,4]],[[],[],[1],[2,1,5]],[[],[],[1],[2,2,2]],[[],[],[1],[2,2,3]],[[],[],[1],[2,2,4]]]

theorem patterns_17_8_15_verified : ∀ D ∈ patterns_17_8_15, PatternVerified 17 8 D := by

  simp only [patterns_17_8_15, List.forall_mem_cons]

  exact ⟨⟨certificate_2460, certificate_2460_valid⟩, ⟨⟨certificate_2461, certificate_2461_valid⟩, ⟨⟨certificate_2462, certificate_2462_valid⟩, ⟨⟨certificate_2463, certificate_2463_valid⟩, ⟨⟨certificate_2464, certificate_2464_valid⟩, ⟨⟨certificate_2465, certificate_2465_valid⟩, ⟨⟨certificate_2466, certificate_2466_valid⟩, ⟨⟨certificate_2467, certificate_2467_valid⟩, ⟨⟨certificate_2468, certificate_2468_valid⟩, ⟨⟨certificate_2469, certificate_2469_valid⟩, ⟨⟨certificate_2470, certificate_2470_valid⟩, ⟨⟨certificate_2471, certificate_2471_valid⟩, ⟨⟨certificate_2472, certificate_2472_valid⟩, ⟨⟨certificate_2473, certificate_2473_valid⟩, ⟨⟨certificate_2474, certificate_2474_valid⟩, ⟨⟨certificate_2475, certificate_2475_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_16 : List (List (List ℕ)) := [[[],[],[1],[2,3,2]],[[],[],[1],[2,3,3]],[[],[],[1],[2,4,2]],[[],[],[1],[3],[3]],[[],[],[1],[3],[4]],[[],[],[1],[3],[5]],[[],[],[1],[3,1,3]],[[],[],[1],[3,1,4]],[[],[],[1],[3,2,3]],[[],[],[1],[4],[4]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[1,4]],[[],[],[1,1],[1,5]],[[],[],[1,1],[1,6]]]

theorem patterns_17_8_16_verified : ∀ D ∈ patterns_17_8_16, PatternVerified 17 8 D := by

  simp only [patterns_17_8_16, List.forall_mem_cons]

  exact ⟨⟨certificate_2476, certificate_2476_valid⟩, ⟨⟨certificate_2477, certificate_2477_valid⟩, ⟨⟨certificate_2478, certificate_2478_valid⟩, ⟨⟨certificate_2479, certificate_2479_valid⟩, ⟨⟨certificate_2480, certificate_2480_valid⟩, ⟨⟨certificate_2481, certificate_2481_valid⟩, ⟨⟨certificate_2482, certificate_2482_valid⟩, ⟨⟨certificate_2483, certificate_2483_valid⟩, ⟨⟨certificate_2484, certificate_2484_valid⟩, ⟨⟨certificate_2485, certificate_2485_valid⟩, ⟨⟨certificate_2486, certificate_2486_valid⟩, ⟨⟨certificate_2487, certificate_2487_valid⟩, ⟨⟨certificate_2488, certificate_2488_valid⟩, ⟨⟨certificate_2489, certificate_2489_valid⟩, ⟨⟨certificate_2490, certificate_2490_valid⟩, ⟨⟨certificate_2491, certificate_2491_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_17 : List (List (List ℕ)) := [[[],[],[1,1],[2,2]],[[],[],[1,1],[2,3]],[[],[],[1,1],[2,4]],[[],[],[1,1],[2,5]],[[],[],[1,1],[3,3]],[[],[],[1,1],[3,4]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]],[[],[],[1,1,1],[4]],[[],[],[1,1,1],[5]],[[],[],[1,1,1],[6]],[[],[],[1,1,1,1,1]],[[],[],[1,1,1,1,2]],[[],[],[1,1,1,1,3]],[[],[],[1,1,1,1,4]],[[],[],[1,1,1,1,5]]]

theorem patterns_17_8_17_verified : ∀ D ∈ patterns_17_8_17, PatternVerified 17 8 D := by

  simp only [patterns_17_8_17, List.forall_mem_cons]

  exact ⟨⟨certificate_2492, certificate_2492_valid⟩, ⟨⟨certificate_2493, certificate_2493_valid⟩, ⟨⟨certificate_2494, certificate_2494_valid⟩, ⟨⟨certificate_2495, certificate_2495_valid⟩, ⟨⟨certificate_2496, certificate_2496_valid⟩, ⟨⟨certificate_2497, certificate_2497_valid⟩, ⟨⟨certificate_2498, certificate_2498_valid⟩, ⟨⟨certificate_2499, certificate_2499_valid⟩, ⟨⟨certificate_2500, certificate_2500_valid⟩, ⟨⟨certificate_2501, certificate_2501_valid⟩, ⟨⟨certificate_2502, certificate_2502_valid⟩, ⟨⟨certificate_2503, certificate_2503_valid⟩, ⟨⟨certificate_2504, certificate_2504_valid⟩, ⟨⟨certificate_2505, certificate_2505_valid⟩, ⟨⟨certificate_2506, certificate_2506_valid⟩, ⟨⟨certificate_2507, certificate_2507_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_18 : List (List (List ℕ)) := [[[],[],[1,1,1,2,1]],[[],[],[1,1,1,2,2]],[[],[],[1,1,1,2,3]],[[],[],[1,1,1,2,4]],[[],[],[1,1,1,3,1]],[[],[],[1,1,1,3,2]],[[],[],[1,1,1,3,3]],[[],[],[1,1,1,4,1]],[[],[],[1,1,1,4,2]],[[],[],[1,1,1,5,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2],[3]],[[],[],[1,1,2],[4]],[[],[],[1,1,2],[5]],[[],[],[1,1,2,1,1]],[[],[],[1,1,2,1,2]]]

theorem patterns_17_8_18_verified : ∀ D ∈ patterns_17_8_18, PatternVerified 17 8 D := by

  simp only [patterns_17_8_18, List.forall_mem_cons]

  exact ⟨⟨certificate_2508, certificate_2508_valid⟩, ⟨⟨certificate_2509, certificate_2509_valid⟩, ⟨⟨certificate_2510, certificate_2510_valid⟩, ⟨⟨certificate_2511, certificate_2511_valid⟩, ⟨⟨certificate_2512, certificate_2512_valid⟩, ⟨⟨certificate_2513, certificate_2513_valid⟩, ⟨⟨certificate_2514, certificate_2514_valid⟩, ⟨⟨certificate_2515, certificate_2515_valid⟩, ⟨⟨certificate_2516, certificate_2516_valid⟩, ⟨⟨certificate_2517, certificate_2517_valid⟩, ⟨⟨certificate_2518, certificate_2518_valid⟩, ⟨⟨certificate_2519, certificate_2519_valid⟩, ⟨⟨certificate_2520, certificate_2520_valid⟩, ⟨⟨certificate_2521, certificate_2521_valid⟩, ⟨⟨certificate_2522, certificate_2522_valid⟩, ⟨⟨certificate_2523, certificate_2523_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_19 : List (List (List ℕ)) := [[[],[],[1,1,2,1,3]],[[],[],[1,1,2,1,4]],[[],[],[1,1,2,2,1]],[[],[],[1,1,2,2,2]],[[],[],[1,1,2,2,3]],[[],[],[1,1,2,3,1]],[[],[],[1,1,2,3,2]],[[],[],[1,1,2,4,1]],[[],[],[1,1,3],[2]],[[],[],[1,1,3],[3]],[[],[],[1,1,3],[4]],[[],[],[1,1,3,1,1]],[[],[],[1,1,3,1,2]],[[],[],[1,1,3,1,3]],[[],[],[1,1,3,2,1]],[[],[],[1,1,3,2,2]]]

theorem patterns_17_8_19_verified : ∀ D ∈ patterns_17_8_19, PatternVerified 17 8 D := by

  simp only [patterns_17_8_19, List.forall_mem_cons]

  exact ⟨⟨certificate_2524, certificate_2524_valid⟩, ⟨⟨certificate_2525, certificate_2525_valid⟩, ⟨⟨certificate_2526, certificate_2526_valid⟩, ⟨⟨certificate_2527, certificate_2527_valid⟩, ⟨⟨certificate_2528, certificate_2528_valid⟩, ⟨⟨certificate_2529, certificate_2529_valid⟩, ⟨⟨certificate_2530, certificate_2530_valid⟩, ⟨⟨certificate_2531, certificate_2531_valid⟩, ⟨⟨certificate_2532, certificate_2532_valid⟩, ⟨⟨certificate_2533, certificate_2533_valid⟩, ⟨⟨certificate_2534, certificate_2534_valid⟩, ⟨⟨certificate_2535, certificate_2535_valid⟩, ⟨⟨certificate_2536, certificate_2536_valid⟩, ⟨⟨certificate_2537, certificate_2537_valid⟩, ⟨⟨certificate_2538, certificate_2538_valid⟩, ⟨⟨certificate_2539, certificate_2539_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_20 : List (List (List ℕ)) := [[[],[],[1,1,3,3,1]],[[],[],[1,1,4],[2]],[[],[],[1,1,4],[3]],[[],[],[1,1,4,1,1]],[[],[],[1,1,4,1,2]],[[],[],[1,1,4,2,1]],[[],[],[1,1,5],[2]],[[],[],[1,1,5,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2],[1,3]],[[],[],[1,2],[1,4]],[[],[],[1,2],[1,5]],[[],[],[1,2],[2,2]],[[],[],[1,2],[2,3]],[[],[],[1,2],[2,4]],[[],[],[1,2],[3,3]]]

theorem patterns_17_8_20_verified : ∀ D ∈ patterns_17_8_20, PatternVerified 17 8 D := by

  simp only [patterns_17_8_20, List.forall_mem_cons]

  exact ⟨⟨certificate_2540, certificate_2540_valid⟩, ⟨⟨certificate_2541, certificate_2541_valid⟩, ⟨⟨certificate_2542, certificate_2542_valid⟩, ⟨⟨certificate_2543, certificate_2543_valid⟩, ⟨⟨certificate_2544, certificate_2544_valid⟩, ⟨⟨certificate_2545, certificate_2545_valid⟩, ⟨⟨certificate_2546, certificate_2546_valid⟩, ⟨⟨certificate_2547, certificate_2547_valid⟩, ⟨⟨certificate_2548, certificate_2548_valid⟩, ⟨⟨certificate_2549, certificate_2549_valid⟩, ⟨⟨certificate_2550, certificate_2550_valid⟩, ⟨⟨certificate_2551, certificate_2551_valid⟩, ⟨⟨certificate_2552, certificate_2552_valid⟩, ⟨⟨certificate_2553, certificate_2553_valid⟩, ⟨⟨certificate_2554, certificate_2554_valid⟩, ⟨⟨certificate_2555, certificate_2555_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_21 : List (List (List ℕ)) := [[[],[],[1,2,1],[2]],[[],[],[1,2,1],[3]],[[],[],[1,2,1],[4]],[[],[],[1,2,1],[5]],[[],[],[1,2,1,1,2]],[[],[],[1,2,1,1,3]],[[],[],[1,2,1,1,4]],[[],[],[1,2,1,2,1]],[[],[],[1,2,1,2,2]],[[],[],[1,2,1,2,3]],[[],[],[1,2,1,3,1]],[[],[],[1,2,1,3,2]],[[],[],[1,2,1,4,1]],[[],[],[1,2,2],[2]],[[],[],[1,2,2],[3]],[[],[],[1,2,2],[4]]]

theorem patterns_17_8_21_verified : ∀ D ∈ patterns_17_8_21, PatternVerified 17 8 D := by

  simp only [patterns_17_8_21, List.forall_mem_cons]

  exact ⟨⟨certificate_2556, certificate_2556_valid⟩, ⟨⟨certificate_2557, certificate_2557_valid⟩, ⟨⟨certificate_2558, certificate_2558_valid⟩, ⟨⟨certificate_2559, certificate_2559_valid⟩, ⟨⟨certificate_2560, certificate_2560_valid⟩, ⟨⟨certificate_2561, certificate_2561_valid⟩, ⟨⟨certificate_2562, certificate_2562_valid⟩, ⟨⟨certificate_2563, certificate_2563_valid⟩, ⟨⟨certificate_2564, certificate_2564_valid⟩, ⟨⟨certificate_2565, certificate_2565_valid⟩, ⟨⟨certificate_2566, certificate_2566_valid⟩, ⟨⟨certificate_2567, certificate_2567_valid⟩, ⟨⟨certificate_2568, certificate_2568_valid⟩, ⟨⟨certificate_2569, certificate_2569_valid⟩, ⟨⟨certificate_2570, certificate_2570_valid⟩, ⟨⟨certificate_2571, certificate_2571_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_22 : List (List (List ℕ)) := [[[],[],[1,2,2,1,2]],[[],[],[1,2,2,1,3]],[[],[],[1,2,2,2,1]],[[],[],[1,2,2,2,2]],[[],[],[1,2,2,3,1]],[[],[],[1,2,3],[2]],[[],[],[1,2,3],[3]],[[],[],[1,2,3,1,2]],[[],[],[1,2,3,2,1]],[[],[],[1,2,4],[2]],[[],[],[1,3],[1,3]],[[],[],[1,3],[1,4]],[[],[],[1,3],[2,2]],[[],[],[1,3],[2,3]],[[],[],[1,3,1],[2]],[[],[],[1,3,1],[3]]]

theorem patterns_17_8_22_verified : ∀ D ∈ patterns_17_8_22, PatternVerified 17 8 D := by

  simp only [patterns_17_8_22, List.forall_mem_cons]

  exact ⟨⟨certificate_2572, certificate_2572_valid⟩, ⟨⟨certificate_2573, certificate_2573_valid⟩, ⟨⟨certificate_2574, certificate_2574_valid⟩, ⟨⟨certificate_2575, certificate_2575_valid⟩, ⟨⟨certificate_2576, certificate_2576_valid⟩, ⟨⟨certificate_2577, certificate_2577_valid⟩, ⟨⟨certificate_2578, certificate_2578_valid⟩, ⟨⟨certificate_2579, certificate_2579_valid⟩, ⟨⟨certificate_2580, certificate_2580_valid⟩, ⟨⟨certificate_2581, certificate_2581_valid⟩, ⟨⟨certificate_2582, certificate_2582_valid⟩, ⟨⟨certificate_2583, certificate_2583_valid⟩, ⟨⟨certificate_2584, certificate_2584_valid⟩, ⟨⟨certificate_2585, certificate_2585_valid⟩, ⟨⟨certificate_2586, certificate_2586_valid⟩, ⟨⟨certificate_2587, certificate_2587_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_23 : List (List (List ℕ)) := [[[],[],[1,3,1],[4]],[[],[],[1,3,1,1,2]],[[],[],[1,3,1,1,3]],[[],[],[1,3,1,2,2]],[[],[],[1,3,1,3,1]],[[],[],[1,3,2],[2]],[[],[],[1,3,2],[3]],[[],[],[1,3,2,1,2]],[[],[],[1,3,3],[2]],[[],[],[1,4],[2,2]],[[],[],[1,4,1],[2]],[[],[],[1,4,1],[3]],[[],[],[1,4,1,1,2]],[[],[],[1,4,2],[2]],[[],[],[1,5,1],[2]],[[],[],[2],[2],[2]]]

theorem patterns_17_8_23_verified : ∀ D ∈ patterns_17_8_23, PatternVerified 17 8 D := by

  simp only [patterns_17_8_23, List.forall_mem_cons]

  exact ⟨⟨certificate_2588, certificate_2588_valid⟩, ⟨⟨certificate_2589, certificate_2589_valid⟩, ⟨⟨certificate_2590, certificate_2590_valid⟩, ⟨⟨certificate_2591, certificate_2591_valid⟩, ⟨⟨certificate_2592, certificate_2592_valid⟩, ⟨⟨certificate_2593, certificate_2593_valid⟩, ⟨⟨certificate_2594, certificate_2594_valid⟩, ⟨⟨certificate_2595, certificate_2595_valid⟩, ⟨⟨certificate_2596, certificate_2596_valid⟩, ⟨⟨certificate_2597, certificate_2597_valid⟩, ⟨⟨certificate_2598, certificate_2598_valid⟩, ⟨⟨certificate_2599, certificate_2599_valid⟩, ⟨⟨certificate_2600, certificate_2600_valid⟩, ⟨⟨certificate_2601, certificate_2601_valid⟩, ⟨⟨certificate_2602, certificate_2602_valid⟩, ⟨⟨certificate_2603, certificate_2603_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_24 : List (List (List ℕ)) := [[[],[],[2],[2],[3]],[[],[],[2],[2],[4]],[[],[],[2],[2],[5]],[[],[],[2],[2,1,2]],[[],[],[2],[2,1,3]],[[],[],[2],[2,1,4]],[[],[],[2],[2,2,2]],[[],[],[2],[2,2,3]],[[],[],[2],[2,3,2]],[[],[],[2],[3],[3]],[[],[],[2],[3],[4]],[[],[],[2],[3,1,3]],[[],[],[2,1,1,1,2]],[[],[],[2,1,1,1,3]],[[],[],[2,1,1,1,4]],[[],[],[2,1,1,2,2]]]

theorem patterns_17_8_24_verified : ∀ D ∈ patterns_17_8_24, PatternVerified 17 8 D := by

  simp only [patterns_17_8_24, List.forall_mem_cons]

  exact ⟨⟨certificate_2604, certificate_2604_valid⟩, ⟨⟨certificate_2605, certificate_2605_valid⟩, ⟨⟨certificate_2606, certificate_2606_valid⟩, ⟨⟨certificate_2607, certificate_2607_valid⟩, ⟨⟨certificate_2608, certificate_2608_valid⟩, ⟨⟨certificate_2609, certificate_2609_valid⟩, ⟨⟨certificate_2610, certificate_2610_valid⟩, ⟨⟨certificate_2611, certificate_2611_valid⟩, ⟨⟨certificate_2612, certificate_2612_valid⟩, ⟨⟨certificate_2613, certificate_2613_valid⟩, ⟨⟨certificate_2614, certificate_2614_valid⟩, ⟨⟨certificate_2615, certificate_2615_valid⟩, ⟨⟨certificate_2616, certificate_2616_valid⟩, ⟨⟨certificate_2617, certificate_2617_valid⟩, ⟨⟨certificate_2618, certificate_2618_valid⟩, ⟨⟨certificate_2619, certificate_2619_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_25 : List (List (List ℕ)) := [[[],[],[2,1,1,2,3]],[[],[],[2,1,1,3,2]],[[],[],[2,1,2],[3]],[[],[],[2,1,2],[4]],[[],[],[2,1,2,1,2]],[[],[],[2,1,2,1,3]],[[],[],[2,1,2,2,2]],[[],[],[2,1,3],[3]],[[],[],[2,1,3,1,2]],[[],[],[2,2],[2,2]],[[],[],[2,2],[2,3]],[[],[],[2,2,1,1,3]],[[],[],[2,2,1,2,2]],[[],[],[2,2,2],[3]],[[],[],[3],[3],[3]],[[],[],[3,1,1,1,3]]]

theorem patterns_17_8_25_verified : ∀ D ∈ patterns_17_8_25, PatternVerified 17 8 D := by

  simp only [patterns_17_8_25, List.forall_mem_cons]

  exact ⟨⟨certificate_2620, certificate_2620_valid⟩, ⟨⟨certificate_2621, certificate_2621_valid⟩, ⟨⟨certificate_2622, certificate_2622_valid⟩, ⟨⟨certificate_2623, certificate_2623_valid⟩, ⟨⟨certificate_2624, certificate_2624_valid⟩, ⟨⟨certificate_2625, certificate_2625_valid⟩, ⟨⟨certificate_2626, certificate_2626_valid⟩, ⟨⟨certificate_2627, certificate_2627_valid⟩, ⟨⟨certificate_2628, certificate_2628_valid⟩, ⟨⟨certificate_2629, certificate_2629_valid⟩, ⟨⟨certificate_2630, certificate_2630_valid⟩, ⟨⟨certificate_2631, certificate_2631_valid⟩, ⟨⟨certificate_2632, certificate_2632_valid⟩, ⟨⟨certificate_2633, certificate_2633_valid⟩, ⟨⟨certificate_2634, certificate_2634_valid⟩, ⟨⟨certificate_2635, certificate_2635_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_26 : List (List (List ℕ)) := [[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[1,4]],[[],[1],[1],[1,5]],[[],[1],[1],[1,6]],[[],[1],[1],[2,2]],[[],[1],[1],[2,3]],[[],[1],[1],[2,4]],[[],[1],[1],[2,5]],[[],[1],[1],[3,3]],[[],[1],[1],[3,4]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]],[[],[1],[1,1],[4]],[[],[1],[1,1],[5]]]

theorem patterns_17_8_26_verified : ∀ D ∈ patterns_17_8_26, PatternVerified 17 8 D := by

  simp only [patterns_17_8_26, List.forall_mem_cons]

  exact ⟨⟨certificate_2636, certificate_2636_valid⟩, ⟨⟨certificate_2637, certificate_2637_valid⟩, ⟨⟨certificate_2638, certificate_2638_valid⟩, ⟨⟨certificate_2639, certificate_2639_valid⟩, ⟨⟨certificate_2640, certificate_2640_valid⟩, ⟨⟨certificate_2641, certificate_2641_valid⟩, ⟨⟨certificate_2642, certificate_2642_valid⟩, ⟨⟨certificate_2643, certificate_2643_valid⟩, ⟨⟨certificate_2644, certificate_2644_valid⟩, ⟨⟨certificate_2645, certificate_2645_valid⟩, ⟨⟨certificate_2646, certificate_2646_valid⟩, ⟨⟨certificate_2647, certificate_2647_valid⟩, ⟨⟨certificate_2648, certificate_2648_valid⟩, ⟨⟨certificate_2649, certificate_2649_valid⟩, ⟨⟨certificate_2650, certificate_2650_valid⟩, ⟨⟨certificate_2651, certificate_2651_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_27 : List (List (List ℕ)) := [[[],[1],[1,1],[6]],[[],[1],[1,1,1,1]],[[],[1],[1,1,1,2]],[[],[1],[1,1,1,3]],[[],[1],[1,1,1,4]],[[],[1],[1,1,1,5]],[[],[1],[1,1,2,1]],[[],[1],[1,1,2,2]],[[],[1],[1,1,2,3]],[[],[1],[1,1,2,4]],[[],[1],[1,1,3,1]],[[],[1],[1,1,3,2]],[[],[1],[1,1,3,3]],[[],[1],[1,1,4,1]],[[],[1],[1,1,4,2]],[[],[1],[1,1,5,1]]]

theorem patterns_17_8_27_verified : ∀ D ∈ patterns_17_8_27, PatternVerified 17 8 D := by

  simp only [patterns_17_8_27, List.forall_mem_cons]

  exact ⟨⟨certificate_2652, certificate_2652_valid⟩, ⟨⟨certificate_2653, certificate_2653_valid⟩, ⟨⟨certificate_2654, certificate_2654_valid⟩, ⟨⟨certificate_2655, certificate_2655_valid⟩, ⟨⟨certificate_2656, certificate_2656_valid⟩, ⟨⟨certificate_2657, certificate_2657_valid⟩, ⟨⟨certificate_2658, certificate_2658_valid⟩, ⟨⟨certificate_2659, certificate_2659_valid⟩, ⟨⟨certificate_2660, certificate_2660_valid⟩, ⟨⟨certificate_2661, certificate_2661_valid⟩, ⟨⟨certificate_2662, certificate_2662_valid⟩, ⟨⟨certificate_2663, certificate_2663_valid⟩, ⟨⟨certificate_2664, certificate_2664_valid⟩, ⟨⟨certificate_2665, certificate_2665_valid⟩, ⟨⟨certificate_2666, certificate_2666_valid⟩, ⟨⟨certificate_2667, certificate_2667_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_28 : List (List (List ℕ)) := [[[],[1],[1,2],[2]],[[],[1],[1,2],[3]],[[],[1],[1,2],[4]],[[],[1],[1,2],[5]],[[],[1],[1,2,1,2]],[[],[1],[1,2,1,3]],[[],[1],[1,2,1,4]],[[],[1],[1,2,2,1]],[[],[1],[1,2,2,2]],[[],[1],[1,2,2,3]],[[],[1],[1,2,3,1]],[[],[1],[1,2,3,2]],[[],[1],[1,2,4,1]],[[],[1],[1,3],[2]],[[],[1],[1,3],[3]],[[],[1],[1,3],[4]]]

theorem patterns_17_8_28_verified : ∀ D ∈ patterns_17_8_28, PatternVerified 17 8 D := by

  simp only [patterns_17_8_28, List.forall_mem_cons]

  exact ⟨⟨certificate_2668, certificate_2668_valid⟩, ⟨⟨certificate_2669, certificate_2669_valid⟩, ⟨⟨certificate_2670, certificate_2670_valid⟩, ⟨⟨certificate_2671, certificate_2671_valid⟩, ⟨⟨certificate_2672, certificate_2672_valid⟩, ⟨⟨certificate_2673, certificate_2673_valid⟩, ⟨⟨certificate_2674, certificate_2674_valid⟩, ⟨⟨certificate_2675, certificate_2675_valid⟩, ⟨⟨certificate_2676, certificate_2676_valid⟩, ⟨⟨certificate_2677, certificate_2677_valid⟩, ⟨⟨certificate_2678, certificate_2678_valid⟩, ⟨⟨certificate_2679, certificate_2679_valid⟩, ⟨⟨certificate_2680, certificate_2680_valid⟩, ⟨⟨certificate_2681, certificate_2681_valid⟩, ⟨⟨certificate_2682, certificate_2682_valid⟩, ⟨⟨certificate_2683, certificate_2683_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_29 : List (List (List ℕ)) := [[[],[1],[1,3,1,2]],[[],[1],[1,3,1,3]],[[],[1],[1,3,2,2]],[[],[1],[1,3,3,1]],[[],[1],[1,4],[2]],[[],[1],[1,4],[3]],[[],[1],[1,4,1,2]],[[],[1],[1,5],[2]],[[],[1],[2],[2,2]],[[],[1],[2],[2,3]],[[],[1],[2],[2,4]],[[],[1],[2],[3,3]],[[],[1],[2,1,1,2]],[[],[1],[2,1,1,3]],[[],[1],[2,1,1,4]],[[],[1],[2,1,2,2]]]

theorem patterns_17_8_29_verified : ∀ D ∈ patterns_17_8_29, PatternVerified 17 8 D := by

  simp only [patterns_17_8_29, List.forall_mem_cons]

  exact ⟨⟨certificate_2684, certificate_2684_valid⟩, ⟨⟨certificate_2685, certificate_2685_valid⟩, ⟨⟨certificate_2686, certificate_2686_valid⟩, ⟨⟨certificate_2687, certificate_2687_valid⟩, ⟨⟨certificate_2688, certificate_2688_valid⟩, ⟨⟨certificate_2689, certificate_2689_valid⟩, ⟨⟨certificate_2690, certificate_2690_valid⟩, ⟨⟨certificate_2691, certificate_2691_valid⟩, ⟨⟨certificate_2692, certificate_2692_valid⟩, ⟨⟨certificate_2693, certificate_2693_valid⟩, ⟨⟨certificate_2694, certificate_2694_valid⟩, ⟨⟨certificate_2695, certificate_2695_valid⟩, ⟨⟨certificate_2696, certificate_2696_valid⟩, ⟨⟨certificate_2697, certificate_2697_valid⟩, ⟨⟨certificate_2698, certificate_2698_valid⟩, ⟨⟨certificate_2699, certificate_2699_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_30 : List (List (List ℕ)) := [[[],[1],[2,1,2,3]],[[],[1],[2,1,3,2]],[[],[1],[2,2],[3]],[[],[1],[2,2],[4]],[[],[1],[2,2,1,3]],[[],[1],[2,2,2,2]],[[],[1],[2,3],[3]],[[],[1],[3,1,1,3]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]],[[],[1,1],[1,1,3]],[[],[1,1],[1,1,4]],[[],[1,1],[1,1,5]],[[],[1,1],[1,2,1]],[[],[1,1],[1,2,2]],[[],[1,1],[1,2,3]]]

theorem patterns_17_8_30_verified : ∀ D ∈ patterns_17_8_30, PatternVerified 17 8 D := by

  simp only [patterns_17_8_30, List.forall_mem_cons]

  exact ⟨⟨certificate_2700, certificate_2700_valid⟩, ⟨⟨certificate_2701, certificate_2701_valid⟩, ⟨⟨certificate_2702, certificate_2702_valid⟩, ⟨⟨certificate_2703, certificate_2703_valid⟩, ⟨⟨certificate_2704, certificate_2704_valid⟩, ⟨⟨certificate_2705, certificate_2705_valid⟩, ⟨⟨certificate_2706, certificate_2706_valid⟩, ⟨⟨certificate_2707, certificate_2707_valid⟩, ⟨⟨certificate_2708, certificate_2708_valid⟩, ⟨⟨certificate_2709, certificate_2709_valid⟩, ⟨⟨certificate_2710, certificate_2710_valid⟩, ⟨⟨certificate_2711, certificate_2711_valid⟩, ⟨⟨certificate_2712, certificate_2712_valid⟩, ⟨⟨certificate_2713, certificate_2713_valid⟩, ⟨⟨certificate_2714, certificate_2714_valid⟩, ⟨⟨certificate_2715, certificate_2715_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_31 : List (List (List ℕ)) := [[[],[1,1],[1,2,4]],[[],[1,1],[1,3,1]],[[],[1,1],[1,3,2]],[[],[1,1],[1,3,3]],[[],[1,1],[1,4,1]],[[],[1,1],[1,4,2]],[[],[1,1],[1,5,1]],[[],[1,1],[2],[2]],[[],[1,1],[2],[3]],[[],[1,1],[2],[4]],[[],[1,1],[2],[5]],[[],[1,1],[2,1,2]],[[],[1,1],[2,1,3]],[[],[1,1],[2,1,4]],[[],[1,1],[2,2,2]],[[],[1,1],[2,2,3]]]

theorem patterns_17_8_31_verified : ∀ D ∈ patterns_17_8_31, PatternVerified 17 8 D := by

  simp only [patterns_17_8_31, List.forall_mem_cons]

  exact ⟨⟨certificate_2716, certificate_2716_valid⟩, ⟨⟨certificate_2717, certificate_2717_valid⟩, ⟨⟨certificate_2718, certificate_2718_valid⟩, ⟨⟨certificate_2719, certificate_2719_valid⟩, ⟨⟨certificate_2720, certificate_2720_valid⟩, ⟨⟨certificate_2721, certificate_2721_valid⟩, ⟨⟨certificate_2722, certificate_2722_valid⟩, ⟨⟨certificate_2723, certificate_2723_valid⟩, ⟨⟨certificate_2724, certificate_2724_valid⟩, ⟨⟨certificate_2725, certificate_2725_valid⟩, ⟨⟨certificate_2726, certificate_2726_valid⟩, ⟨⟨certificate_2727, certificate_2727_valid⟩, ⟨⟨certificate_2728, certificate_2728_valid⟩, ⟨⟨certificate_2729, certificate_2729_valid⟩, ⟨⟨certificate_2730, certificate_2730_valid⟩, ⟨⟨certificate_2731, certificate_2731_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_32 : List (List (List ℕ)) := [[[],[1,1],[2,3,2]],[[],[1,1],[3],[3]],[[],[1,1],[3],[4]],[[],[1,1],[3,1,3]],[[],[1,1,1],[1,2]],[[],[1,1,1],[1,3]],[[],[1,1,1],[1,4]],[[],[1,1,1],[1,5]],[[],[1,1,1],[2,2]],[[],[1,1,1],[2,3]],[[],[1,1,1],[2,4]],[[],[1,1,1],[3,3]],[[],[1,1,1,1],[2]],[[],[1,1,1,1],[3]],[[],[1,1,1,1],[4]],[[],[1,1,1,1],[5]]]

theorem patterns_17_8_32_verified : ∀ D ∈ patterns_17_8_32, PatternVerified 17 8 D := by

  simp only [patterns_17_8_32, List.forall_mem_cons]

  exact ⟨⟨certificate_2732, certificate_2732_valid⟩, ⟨⟨certificate_2733, certificate_2733_valid⟩, ⟨⟨certificate_2734, certificate_2734_valid⟩, ⟨⟨certificate_2735, certificate_2735_valid⟩, ⟨⟨certificate_2736, certificate_2736_valid⟩, ⟨⟨certificate_2737, certificate_2737_valid⟩, ⟨⟨certificate_2738, certificate_2738_valid⟩, ⟨⟨certificate_2739, certificate_2739_valid⟩, ⟨⟨certificate_2740, certificate_2740_valid⟩, ⟨⟨certificate_2741, certificate_2741_valid⟩, ⟨⟨certificate_2742, certificate_2742_valid⟩, ⟨⟨certificate_2743, certificate_2743_valid⟩, ⟨⟨certificate_2744, certificate_2744_valid⟩, ⟨⟨certificate_2745, certificate_2745_valid⟩, ⟨⟨certificate_2746, certificate_2746_valid⟩, ⟨⟨certificate_2747, certificate_2747_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_33 : List (List (List ℕ)) := [[[],[1,1,1,1,1,1]],[[],[1,1,1,1,1,2]],[[],[1,1,1,1,1,3]],[[],[1,1,1,1,1,4]],[[],[1,1,1,1,2,1]],[[],[1,1,1,1,2,2]],[[],[1,1,1,1,2,3]],[[],[1,1,1,1,3,1]],[[],[1,1,1,1,3,2]],[[],[1,1,1,1,4,1]],[[],[1,1,1,2],[2]],[[],[1,1,1,2],[3]],[[],[1,1,1,2],[4]],[[],[1,1,1,2,1,1]],[[],[1,1,1,2,1,2]],[[],[1,1,1,2,1,3]]]

theorem patterns_17_8_33_verified : ∀ D ∈ patterns_17_8_33, PatternVerified 17 8 D := by

  simp only [patterns_17_8_33, List.forall_mem_cons]

  exact ⟨⟨certificate_2748, certificate_2748_valid⟩, ⟨⟨certificate_2749, certificate_2749_valid⟩, ⟨⟨certificate_2750, certificate_2750_valid⟩, ⟨⟨certificate_2751, certificate_2751_valid⟩, ⟨⟨certificate_2752, certificate_2752_valid⟩, ⟨⟨certificate_2753, certificate_2753_valid⟩, ⟨⟨certificate_2754, certificate_2754_valid⟩, ⟨⟨certificate_2755, certificate_2755_valid⟩, ⟨⟨certificate_2756, certificate_2756_valid⟩, ⟨⟨certificate_2757, certificate_2757_valid⟩, ⟨⟨certificate_2758, certificate_2758_valid⟩, ⟨⟨certificate_2759, certificate_2759_valid⟩, ⟨⟨certificate_2760, certificate_2760_valid⟩, ⟨⟨certificate_2761, certificate_2761_valid⟩, ⟨⟨certificate_2762, certificate_2762_valid⟩, ⟨⟨certificate_2763, certificate_2763_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_34 : List (List (List ℕ)) := [[[],[1,1,1,2,2,1]],[[],[1,1,1,2,2,2]],[[],[1,1,1,2,3,1]],[[],[1,1,1,3],[2]],[[],[1,1,1,3],[3]],[[],[1,1,1,3,1,1]],[[],[1,1,1,3,1,2]],[[],[1,1,1,3,2,1]],[[],[1,1,1,4],[2]],[[],[1,1,1,4,1,1]],[[],[1,1,2],[1,2]],[[],[1,1,2],[1,3]],[[],[1,1,2],[1,4]],[[],[1,1,2],[2,2]],[[],[1,1,2],[2,3]],[[],[1,1,2,1],[2]]]

theorem patterns_17_8_34_verified : ∀ D ∈ patterns_17_8_34, PatternVerified 17 8 D := by

  simp only [patterns_17_8_34, List.forall_mem_cons]

  exact ⟨⟨certificate_2764, certificate_2764_valid⟩, ⟨⟨certificate_2765, certificate_2765_valid⟩, ⟨⟨certificate_2766, certificate_2766_valid⟩, ⟨⟨certificate_2767, certificate_2767_valid⟩, ⟨⟨certificate_2768, certificate_2768_valid⟩, ⟨⟨certificate_2769, certificate_2769_valid⟩, ⟨⟨certificate_2770, certificate_2770_valid⟩, ⟨⟨certificate_2771, certificate_2771_valid⟩, ⟨⟨certificate_2772, certificate_2772_valid⟩, ⟨⟨certificate_2773, certificate_2773_valid⟩, ⟨⟨certificate_2774, certificate_2774_valid⟩, ⟨⟨certificate_2775, certificate_2775_valid⟩, ⟨⟨certificate_2776, certificate_2776_valid⟩, ⟨⟨certificate_2777, certificate_2777_valid⟩, ⟨⟨certificate_2778, certificate_2778_valid⟩, ⟨⟨certificate_2779, certificate_2779_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_35 : List (List (List ℕ)) := [[[],[1,1,2,1],[3]],[[],[1,1,2,1],[4]],[[],[1,1,2,1,1,2]],[[],[1,1,2,1,1,3]],[[],[1,1,2,1,2,1]],[[],[1,1,2,1,2,2]],[[],[1,1,2,1,3,1]],[[],[1,1,2,2],[2]],[[],[1,1,2,2],[3]],[[],[1,1,2,2,1,1]],[[],[1,1,2,2,1,2]],[[],[1,1,2,2,2,1]],[[],[1,1,2,3],[2]],[[],[1,1,2,3,1,1]],[[],[1,1,3],[1,2]],[[],[1,1,3],[1,3]]]

theorem patterns_17_8_35_verified : ∀ D ∈ patterns_17_8_35, PatternVerified 17 8 D := by

  simp only [patterns_17_8_35, List.forall_mem_cons]

  exact ⟨⟨certificate_2780, certificate_2780_valid⟩, ⟨⟨certificate_2781, certificate_2781_valid⟩, ⟨⟨certificate_2782, certificate_2782_valid⟩, ⟨⟨certificate_2783, certificate_2783_valid⟩, ⟨⟨certificate_2784, certificate_2784_valid⟩, ⟨⟨certificate_2785, certificate_2785_valid⟩, ⟨⟨certificate_2786, certificate_2786_valid⟩, ⟨⟨certificate_2787, certificate_2787_valid⟩, ⟨⟨certificate_2788, certificate_2788_valid⟩, ⟨⟨certificate_2789, certificate_2789_valid⟩, ⟨⟨certificate_2790, certificate_2790_valid⟩, ⟨⟨certificate_2791, certificate_2791_valid⟩, ⟨⟨certificate_2792, certificate_2792_valid⟩, ⟨⟨certificate_2793, certificate_2793_valid⟩, ⟨⟨certificate_2794, certificate_2794_valid⟩, ⟨⟨certificate_2795, certificate_2795_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_36 : List (List (List ℕ)) := [[[],[1,1,3],[2,2]],[[],[1,1,3,1],[2]],[[],[1,1,3,1],[3]],[[],[1,1,3,1,1,2]],[[],[1,1,3,1,2,1]],[[],[1,1,3,2],[2]],[[],[1,1,4],[1,2]],[[],[1,1,4,1],[2]],[[],[1,2],[1,2,1]],[[],[1,2],[1,2,2]],[[],[1,2],[1,2,3]],[[],[1,2],[1,3,1]],[[],[1,2],[1,3,2]],[[],[1,2],[1,4,1]],[[],[1,2],[2],[2]],[[],[1,2],[2],[3]]]

theorem patterns_17_8_36_verified : ∀ D ∈ patterns_17_8_36, PatternVerified 17 8 D := by

  simp only [patterns_17_8_36, List.forall_mem_cons]

  exact ⟨⟨certificate_2796, certificate_2796_valid⟩, ⟨⟨certificate_2797, certificate_2797_valid⟩, ⟨⟨certificate_2798, certificate_2798_valid⟩, ⟨⟨certificate_2799, certificate_2799_valid⟩, ⟨⟨certificate_2800, certificate_2800_valid⟩, ⟨⟨certificate_2801, certificate_2801_valid⟩, ⟨⟨certificate_2802, certificate_2802_valid⟩, ⟨⟨certificate_2803, certificate_2803_valid⟩, ⟨⟨certificate_2804, certificate_2804_valid⟩, ⟨⟨certificate_2805, certificate_2805_valid⟩, ⟨⟨certificate_2806, certificate_2806_valid⟩, ⟨⟨certificate_2807, certificate_2807_valid⟩, ⟨⟨certificate_2808, certificate_2808_valid⟩, ⟨⟨certificate_2809, certificate_2809_valid⟩, ⟨⟨certificate_2810, certificate_2810_valid⟩, ⟨⟨certificate_2811, certificate_2811_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_37 : List (List (List ℕ)) := [[[],[1,2],[2],[4]],[[],[1,2],[2,1,2]],[[],[1,2],[2,1,3]],[[],[1,2],[2,2,2]],[[],[1,2],[3],[3]],[[],[1,2,1],[1,3]],[[],[1,2,1],[1,4]],[[],[1,2,1],[2,2]],[[],[1,2,1],[2,3]],[[],[1,2,1,1,1,2]],[[],[1,2,1,1,1,3]],[[],[1,2,1,1,2,1]],[[],[1,2,1,1,2,2]],[[],[1,2,1,1,3,1]],[[],[1,2,1,2],[2]],[[],[1,2,1,2],[3]]]

theorem patterns_17_8_37_verified : ∀ D ∈ patterns_17_8_37, PatternVerified 17 8 D := by

  simp only [patterns_17_8_37, List.forall_mem_cons]

  exact ⟨⟨certificate_2812, certificate_2812_valid⟩, ⟨⟨certificate_2813, certificate_2813_valid⟩, ⟨⟨certificate_2814, certificate_2814_valid⟩, ⟨⟨certificate_2815, certificate_2815_valid⟩, ⟨⟨certificate_2816, certificate_2816_valid⟩, ⟨⟨certificate_2817, certificate_2817_valid⟩, ⟨⟨certificate_2818, certificate_2818_valid⟩, ⟨⟨certificate_2819, certificate_2819_valid⟩, ⟨⟨certificate_2820, certificate_2820_valid⟩, ⟨⟨certificate_2821, certificate_2821_valid⟩, ⟨⟨certificate_2822, certificate_2822_valid⟩, ⟨⟨certificate_2823, certificate_2823_valid⟩, ⟨⟨certificate_2824, certificate_2824_valid⟩, ⟨⟨certificate_2825, certificate_2825_valid⟩, ⟨⟨certificate_2826, certificate_2826_valid⟩, ⟨⟨certificate_2827, certificate_2827_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_38 : List (List (List ℕ)) := [[[],[1,2,1,2,1,2]],[[],[1,2,1,2,2,1]],[[],[1,2,1,3],[2]],[[],[1,2,2],[1,3]],[[],[1,2,2],[2,2]],[[],[1,2,2,1],[2]],[[],[1,2,2,1],[3]],[[],[1,2,2,1,1,2]],[[],[1,2,2,2],[2]],[[],[1,2,3,1],[2]],[[],[1,3],[1,3,1]],[[],[1,3],[2],[2]],[[],[1,3],[2],[3]],[[],[1,3],[2,1,2]],[[],[1,3,1],[2,2]],[[],[1,3,1,1,1,2]]]

theorem patterns_17_8_38_verified : ∀ D ∈ patterns_17_8_38, PatternVerified 17 8 D := by

  simp only [patterns_17_8_38, List.forall_mem_cons]

  exact ⟨⟨certificate_2828, certificate_2828_valid⟩, ⟨⟨certificate_2829, certificate_2829_valid⟩, ⟨⟨certificate_2830, certificate_2830_valid⟩, ⟨⟨certificate_2831, certificate_2831_valid⟩, ⟨⟨certificate_2832, certificate_2832_valid⟩, ⟨⟨certificate_2833, certificate_2833_valid⟩, ⟨⟨certificate_2834, certificate_2834_valid⟩, ⟨⟨certificate_2835, certificate_2835_valid⟩, ⟨⟨certificate_2836, certificate_2836_valid⟩, ⟨⟨certificate_2837, certificate_2837_valid⟩, ⟨⟨certificate_2838, certificate_2838_valid⟩, ⟨⟨certificate_2839, certificate_2839_valid⟩, ⟨⟨certificate_2840, certificate_2840_valid⟩, ⟨⟨certificate_2841, certificate_2841_valid⟩, ⟨⟨certificate_2842, certificate_2842_valid⟩, ⟨⟨certificate_2843, certificate_2843_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_39 : List (List (List ℕ)) := [[[],[1,3,1,2],[2]],[[],[1,4],[2],[2]],[[],[2],[2],[2,2]],[[],[2],[2],[2,3]],[[],[2],[2,1,1,2]],[[],[2],[2,1,1,3]],[[],[2],[2,1,2,2]],[[],[2],[2,2],[3]],[[],[2,1,1,1,1,2]],[[],[2,1,1,1,1,3]],[[],[2,1,1,1,2,2]],[[],[2,1,1,2],[3]],[[],[2,1,1,2,1,2]],[[],[2,1,2],[2,2]],[[1],[1],[1],[1]],[[1],[1],[1],[2]]]

theorem patterns_17_8_39_verified : ∀ D ∈ patterns_17_8_39, PatternVerified 17 8 D := by

  simp only [patterns_17_8_39, List.forall_mem_cons]

  exact ⟨⟨certificate_2844, certificate_2844_valid⟩, ⟨⟨certificate_2845, certificate_2845_valid⟩, ⟨⟨certificate_2846, certificate_2846_valid⟩, ⟨⟨certificate_2847, certificate_2847_valid⟩, ⟨⟨certificate_2848, certificate_2848_valid⟩, ⟨⟨certificate_2849, certificate_2849_valid⟩, ⟨⟨certificate_2850, certificate_2850_valid⟩, ⟨⟨certificate_2851, certificate_2851_valid⟩, ⟨⟨certificate_2852, certificate_2852_valid⟩, ⟨⟨certificate_2853, certificate_2853_valid⟩, ⟨⟨certificate_2854, certificate_2854_valid⟩, ⟨⟨certificate_2855, certificate_2855_valid⟩, ⟨⟨certificate_2856, certificate_2856_valid⟩, ⟨⟨certificate_2857, certificate_2857_valid⟩, ⟨⟨certificate_2858, certificate_2858_valid⟩, ⟨⟨certificate_2859, certificate_2859_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_40 : List (List (List ℕ)) := [[[1],[1],[1],[3]],[[1],[1],[1],[4]],[[1],[1],[1],[5]],[[1],[1],[1],[6]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,1,3]],[[1],[1],[1,1,4]],[[1],[1],[1,1,5]],[[1],[1],[1,2,1]],[[1],[1],[1,2,2]],[[1],[1],[1,2,3]],[[1],[1],[1,2,4]],[[1],[1],[1,3,1]],[[1],[1],[1,3,2]],[[1],[1],[1,3,3]]]

theorem patterns_17_8_40_verified : ∀ D ∈ patterns_17_8_40, PatternVerified 17 8 D := by

  simp only [patterns_17_8_40, List.forall_mem_cons]

  exact ⟨⟨certificate_2860, certificate_2860_valid⟩, ⟨⟨certificate_2861, certificate_2861_valid⟩, ⟨⟨certificate_2862, certificate_2862_valid⟩, ⟨⟨certificate_2863, certificate_2863_valid⟩, ⟨⟨certificate_2864, certificate_2864_valid⟩, ⟨⟨certificate_2865, certificate_2865_valid⟩, ⟨⟨certificate_2866, certificate_2866_valid⟩, ⟨⟨certificate_2867, certificate_2867_valid⟩, ⟨⟨certificate_2868, certificate_2868_valid⟩, ⟨⟨certificate_2869, certificate_2869_valid⟩, ⟨⟨certificate_2870, certificate_2870_valid⟩, ⟨⟨certificate_2871, certificate_2871_valid⟩, ⟨⟨certificate_2872, certificate_2872_valid⟩, ⟨⟨certificate_2873, certificate_2873_valid⟩, ⟨⟨certificate_2874, certificate_2874_valid⟩, ⟨⟨certificate_2875, certificate_2875_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_41 : List (List (List ℕ)) := [[[1],[1],[1,4,1]],[[1],[1],[1,4,2]],[[1],[1],[1,5,1]],[[1],[1],[2],[2]],[[1],[1],[2],[3]],[[1],[1],[2],[4]],[[1],[1],[2],[5]],[[1],[1],[2,1,2]],[[1],[1],[2,1,3]],[[1],[1],[2,1,4]],[[1],[1],[2,2,2]],[[1],[1],[2,2,3]],[[1],[1],[2,3,2]],[[1],[1],[3],[3]],[[1],[1],[3],[4]],[[1],[1],[3,1,3]]]

theorem patterns_17_8_41_verified : ∀ D ∈ patterns_17_8_41, PatternVerified 17 8 D := by

  simp only [patterns_17_8_41, List.forall_mem_cons]

  exact ⟨⟨certificate_2876, certificate_2876_valid⟩, ⟨⟨certificate_2877, certificate_2877_valid⟩, ⟨⟨certificate_2878, certificate_2878_valid⟩, ⟨⟨certificate_2879, certificate_2879_valid⟩, ⟨⟨certificate_2880, certificate_2880_valid⟩, ⟨⟨certificate_2881, certificate_2881_valid⟩, ⟨⟨certificate_2882, certificate_2882_valid⟩, ⟨⟨certificate_2883, certificate_2883_valid⟩, ⟨⟨certificate_2884, certificate_2884_valid⟩, ⟨⟨certificate_2885, certificate_2885_valid⟩, ⟨⟨certificate_2886, certificate_2886_valid⟩, ⟨⟨certificate_2887, certificate_2887_valid⟩, ⟨⟨certificate_2888, certificate_2888_valid⟩, ⟨⟨certificate_2889, certificate_2889_valid⟩, ⟨⟨certificate_2890, certificate_2890_valid⟩, ⟨⟨certificate_2891, certificate_2891_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_42 : List (List (List ℕ)) := [[[1],[1,1],[1,1]],[[1],[1,1],[1,2]],[[1],[1,1],[1,3]],[[1],[1,1],[1,4]],[[1],[1,1],[1,5]],[[1],[1,1],[2,2]],[[1],[1,1],[2,3]],[[1],[1,1],[2,4]],[[1],[1,1],[3,3]],[[1],[1,1,1],[2]],[[1],[1,1,1],[3]],[[1],[1,1,1],[4]],[[1],[1,1,1],[5]],[[1],[1,1,1,1,1]],[[1],[1,1,1,1,2]],[[1],[1,1,1,1,3]]]

theorem patterns_17_8_42_verified : ∀ D ∈ patterns_17_8_42, PatternVerified 17 8 D := by

  simp only [patterns_17_8_42, List.forall_mem_cons]

  exact ⟨⟨certificate_2892, certificate_2892_valid⟩, ⟨⟨certificate_2893, certificate_2893_valid⟩, ⟨⟨certificate_2894, certificate_2894_valid⟩, ⟨⟨certificate_2895, certificate_2895_valid⟩, ⟨⟨certificate_2896, certificate_2896_valid⟩, ⟨⟨certificate_2897, certificate_2897_valid⟩, ⟨⟨certificate_2898, certificate_2898_valid⟩, ⟨⟨certificate_2899, certificate_2899_valid⟩, ⟨⟨certificate_2900, certificate_2900_valid⟩, ⟨⟨certificate_2901, certificate_2901_valid⟩, ⟨⟨certificate_2902, certificate_2902_valid⟩, ⟨⟨certificate_2903, certificate_2903_valid⟩, ⟨⟨certificate_2904, certificate_2904_valid⟩, ⟨⟨certificate_2905, certificate_2905_valid⟩, ⟨⟨certificate_2906, certificate_2906_valid⟩, ⟨⟨certificate_2907, certificate_2907_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_43 : List (List (List ℕ)) := [[[1],[1,1,1,1,4]],[[1],[1,1,1,2,1]],[[1],[1,1,1,2,2]],[[1],[1,1,1,2,3]],[[1],[1,1,1,3,1]],[[1],[1,1,1,3,2]],[[1],[1,1,1,4,1]],[[1],[1,1,2],[2]],[[1],[1,1,2],[3]],[[1],[1,1,2],[4]],[[1],[1,1,2,1,1]],[[1],[1,1,2,1,2]],[[1],[1,1,2,1,3]],[[1],[1,1,2,2,1]],[[1],[1,1,2,2,2]],[[1],[1,1,2,3,1]]]

theorem patterns_17_8_43_verified : ∀ D ∈ patterns_17_8_43, PatternVerified 17 8 D := by

  simp only [patterns_17_8_43, List.forall_mem_cons]

  exact ⟨⟨certificate_2908, certificate_2908_valid⟩, ⟨⟨certificate_2909, certificate_2909_valid⟩, ⟨⟨certificate_2910, certificate_2910_valid⟩, ⟨⟨certificate_2911, certificate_2911_valid⟩, ⟨⟨certificate_2912, certificate_2912_valid⟩, ⟨⟨certificate_2913, certificate_2913_valid⟩, ⟨⟨certificate_2914, certificate_2914_valid⟩, ⟨⟨certificate_2915, certificate_2915_valid⟩, ⟨⟨certificate_2916, certificate_2916_valid⟩, ⟨⟨certificate_2917, certificate_2917_valid⟩, ⟨⟨certificate_2918, certificate_2918_valid⟩, ⟨⟨certificate_2919, certificate_2919_valid⟩, ⟨⟨certificate_2920, certificate_2920_valid⟩, ⟨⟨certificate_2921, certificate_2921_valid⟩, ⟨⟨certificate_2922, certificate_2922_valid⟩, ⟨⟨certificate_2923, certificate_2923_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_44 : List (List (List ℕ)) := [[[1],[1,1,3],[2]],[[1],[1,1,3],[3]],[[1],[1,1,3,1,1]],[[1],[1,1,3,1,2]],[[1],[1,1,3,2,1]],[[1],[1,1,4],[2]],[[1],[1,1,4,1,1]],[[1],[1,2],[1,2]],[[1],[1,2],[1,3]],[[1],[1,2],[1,4]],[[1],[1,2],[2,2]],[[1],[1,2],[2,3]],[[1],[1,2,1],[2]],[[1],[1,2,1],[3]],[[1],[1,2,1],[4]],[[1],[1,2,1,1,2]]]

theorem patterns_17_8_44_verified : ∀ D ∈ patterns_17_8_44, PatternVerified 17 8 D := by

  simp only [patterns_17_8_44, List.forall_mem_cons]

  exact ⟨⟨certificate_2924, certificate_2924_valid⟩, ⟨⟨certificate_2925, certificate_2925_valid⟩, ⟨⟨certificate_2926, certificate_2926_valid⟩, ⟨⟨certificate_2927, certificate_2927_valid⟩, ⟨⟨certificate_2928, certificate_2928_valid⟩, ⟨⟨certificate_2929, certificate_2929_valid⟩, ⟨⟨certificate_2930, certificate_2930_valid⟩, ⟨⟨certificate_2931, certificate_2931_valid⟩, ⟨⟨certificate_2932, certificate_2932_valid⟩, ⟨⟨certificate_2933, certificate_2933_valid⟩, ⟨⟨certificate_2934, certificate_2934_valid⟩, ⟨⟨certificate_2935, certificate_2935_valid⟩, ⟨⟨certificate_2936, certificate_2936_valid⟩, ⟨⟨certificate_2937, certificate_2937_valid⟩, ⟨⟨certificate_2938, certificate_2938_valid⟩, ⟨⟨certificate_2939, certificate_2939_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_45 : List (List (List ℕ)) := [[[1],[1,2,1,1,3]],[[1],[1,2,1,2,1]],[[1],[1,2,1,2,2]],[[1],[1,2,1,3,1]],[[1],[1,2,2],[2]],[[1],[1,2,2],[3]],[[1],[1,2,2,1,2]],[[1],[1,2,2,2,1]],[[1],[1,2,3],[2]],[[1],[1,3],[1,3]],[[1],[1,3],[2,2]],[[1],[1,3,1],[2]],[[1],[1,3,1],[3]],[[1],[1,3,1,1,2]],[[1],[1,3,2],[2]],[[1],[1,4,1],[2]]]

theorem patterns_17_8_45_verified : ∀ D ∈ patterns_17_8_45, PatternVerified 17 8 D := by

  simp only [patterns_17_8_45, List.forall_mem_cons]

  exact ⟨⟨certificate_2940, certificate_2940_valid⟩, ⟨⟨certificate_2941, certificate_2941_valid⟩, ⟨⟨certificate_2942, certificate_2942_valid⟩, ⟨⟨certificate_2943, certificate_2943_valid⟩, ⟨⟨certificate_2944, certificate_2944_valid⟩, ⟨⟨certificate_2945, certificate_2945_valid⟩, ⟨⟨certificate_2946, certificate_2946_valid⟩, ⟨⟨certificate_2947, certificate_2947_valid⟩, ⟨⟨certificate_2948, certificate_2948_valid⟩, ⟨⟨certificate_2949, certificate_2949_valid⟩, ⟨⟨certificate_2950, certificate_2950_valid⟩, ⟨⟨certificate_2951, certificate_2951_valid⟩, ⟨⟨certificate_2952, certificate_2952_valid⟩, ⟨⟨certificate_2953, certificate_2953_valid⟩, ⟨⟨certificate_2954, certificate_2954_valid⟩, ⟨⟨certificate_2955, certificate_2955_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_46 : List (List (List ℕ)) := [[[1],[2],[2],[2]],[[1],[2],[2],[3]],[[1],[2],[2],[4]],[[1],[2],[2,1,2]],[[1],[2],[2,1,3]],[[1],[2],[2,2,2]],[[1],[2],[3],[3]],[[1],[2,1,1,1,2]],[[1],[2,1,1,1,3]],[[1],[2,1,1,2,2]],[[1],[2,1,2],[3]],[[1],[2,1,2,1,2]],[[1],[2,2],[2,2]],[[1,1],[1,1],[2]],[[1,1],[1,1],[3]],[[1,1],[1,1],[4]]]

theorem patterns_17_8_46_verified : ∀ D ∈ patterns_17_8_46, PatternVerified 17 8 D := by

  simp only [patterns_17_8_46, List.forall_mem_cons]

  exact ⟨⟨certificate_2956, certificate_2956_valid⟩, ⟨⟨certificate_2957, certificate_2957_valid⟩, ⟨⟨certificate_2958, certificate_2958_valid⟩, ⟨⟨certificate_2959, certificate_2959_valid⟩, ⟨⟨certificate_2960, certificate_2960_valid⟩, ⟨⟨certificate_2961, certificate_2961_valid⟩, ⟨⟨certificate_2962, certificate_2962_valid⟩, ⟨⟨certificate_2963, certificate_2963_valid⟩, ⟨⟨certificate_2964, certificate_2964_valid⟩, ⟨⟨certificate_2965, certificate_2965_valid⟩, ⟨⟨certificate_2966, certificate_2966_valid⟩, ⟨⟨certificate_2967, certificate_2967_valid⟩, ⟨⟨certificate_2968, certificate_2968_valid⟩, ⟨⟨certificate_2969, certificate_2969_valid⟩, ⟨⟨certificate_2970, certificate_2970_valid⟩, ⟨⟨certificate_2971, certificate_2971_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_47 : List (List (List ℕ)) := [[[1,1],[1,1],[5]],[[1,1],[1,1,1,1]],[[1,1],[1,1,1,2]],[[1,1],[1,1,1,3]],[[1,1],[1,1,1,4]],[[1,1],[1,1,2,1]],[[1,1],[1,1,2,2]],[[1,1],[1,1,2,3]],[[1,1],[1,1,3,1]],[[1,1],[1,1,3,2]],[[1,1],[1,1,4,1]],[[1,1],[1,2],[2]],[[1,1],[1,2],[3]],[[1,1],[1,2],[4]],[[1,1],[1,2,1,2]],[[1,1],[1,2,1,3]]]

theorem patterns_17_8_47_verified : ∀ D ∈ patterns_17_8_47, PatternVerified 17 8 D := by

  simp only [patterns_17_8_47, List.forall_mem_cons]

  exact ⟨⟨certificate_2972, certificate_2972_valid⟩, ⟨⟨certificate_2973, certificate_2973_valid⟩, ⟨⟨certificate_2974, certificate_2974_valid⟩, ⟨⟨certificate_2975, certificate_2975_valid⟩, ⟨⟨certificate_2976, certificate_2976_valid⟩, ⟨⟨certificate_2977, certificate_2977_valid⟩, ⟨⟨certificate_2978, certificate_2978_valid⟩, ⟨⟨certificate_2979, certificate_2979_valid⟩, ⟨⟨certificate_2980, certificate_2980_valid⟩, ⟨⟨certificate_2981, certificate_2981_valid⟩, ⟨⟨certificate_2982, certificate_2982_valid⟩, ⟨⟨certificate_2983, certificate_2983_valid⟩, ⟨⟨certificate_2984, certificate_2984_valid⟩, ⟨⟨certificate_2985, certificate_2985_valid⟩, ⟨⟨certificate_2986, certificate_2986_valid⟩, ⟨⟨certificate_2987, certificate_2987_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_48 : List (List (List ℕ)) := [[[1,1],[1,2,2,1]],[[1,1],[1,2,2,2]],[[1,1],[1,2,3,1]],[[1,1],[1,3],[2]],[[1,1],[1,3],[3]],[[1,1],[1,3,1,2]],[[1,1],[1,4],[2]],[[1,1],[2],[2,2]],[[1,1],[2],[2,3]],[[1,1],[2,1,1,2]],[[1,1],[2,1,1,3]],[[1,1],[2,1,2,2]],[[1,1],[2,2],[3]],[[1,1,1],[1,1,1]],[[1,1,1],[1,1,2]],[[1,1,1],[1,1,3]]]

theorem patterns_17_8_48_verified : ∀ D ∈ patterns_17_8_48, PatternVerified 17 8 D := by

  simp only [patterns_17_8_48, List.forall_mem_cons]

  exact ⟨⟨certificate_2988, certificate_2988_valid⟩, ⟨⟨certificate_2989, certificate_2989_valid⟩, ⟨⟨certificate_2990, certificate_2990_valid⟩, ⟨⟨certificate_2991, certificate_2991_valid⟩, ⟨⟨certificate_2992, certificate_2992_valid⟩, ⟨⟨certificate_2993, certificate_2993_valid⟩, ⟨⟨certificate_2994, certificate_2994_valid⟩, ⟨⟨certificate_2995, certificate_2995_valid⟩, ⟨⟨certificate_2996, certificate_2996_valid⟩, ⟨⟨certificate_2997, certificate_2997_valid⟩, ⟨⟨certificate_2998, certificate_2998_valid⟩, ⟨⟨certificate_2999, certificate_2999_valid⟩, ⟨⟨certificate_3000, certificate_3000_valid⟩, ⟨⟨certificate_3001, certificate_3001_valid⟩, ⟨⟨certificate_3002, certificate_3002_valid⟩, ⟨⟨certificate_3003, certificate_3003_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_49 : List (List (List ℕ)) := [[[1,1,1],[1,1,4]],[[1,1,1],[1,2,1]],[[1,1,1],[1,2,2]],[[1,1,1],[1,2,3]],[[1,1,1],[1,3,1]],[[1,1,1],[1,3,2]],[[1,1,1],[1,4,1]],[[1,1,1],[2],[2]],[[1,1,1],[2],[3]],[[1,1,1],[2],[4]],[[1,1,1],[2,1,2]],[[1,1,1],[2,1,3]],[[1,1,1],[2,2,2]],[[1,1,1],[3],[3]],[[1,1,1,1],[1,2]],[[1,1,1,1],[1,3]]]

theorem patterns_17_8_49_verified : ∀ D ∈ patterns_17_8_49, PatternVerified 17 8 D := by

  simp only [patterns_17_8_49, List.forall_mem_cons]

  exact ⟨⟨certificate_3004, certificate_3004_valid⟩, ⟨⟨certificate_3005, certificate_3005_valid⟩, ⟨⟨certificate_3006, certificate_3006_valid⟩, ⟨⟨certificate_3007, certificate_3007_valid⟩, ⟨⟨certificate_3008, certificate_3008_valid⟩, ⟨⟨certificate_3009, certificate_3009_valid⟩, ⟨⟨certificate_3010, certificate_3010_valid⟩, ⟨⟨certificate_3011, certificate_3011_valid⟩, ⟨⟨certificate_3012, certificate_3012_valid⟩, ⟨⟨certificate_3013, certificate_3013_valid⟩, ⟨⟨certificate_3014, certificate_3014_valid⟩, ⟨⟨certificate_3015, certificate_3015_valid⟩, ⟨⟨certificate_3016, certificate_3016_valid⟩, ⟨⟨certificate_3017, certificate_3017_valid⟩, ⟨⟨certificate_3018, certificate_3018_valid⟩, ⟨⟨certificate_3019, certificate_3019_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_50 : List (List (List ℕ)) := [[[1,1,1,1],[1,4]],[[1,1,1,1],[2,2]],[[1,1,1,1],[2,3]],[[1,1,1,1,1],[2]],[[1,1,1,1,1],[3]],[[1,1,1,1,1],[4]],[[1,1,1,1,1,1,1]],[[1,1,1,1,1,1,2]],[[1,1,1,1,1,1,3]],[[1,1,1,1,1,2,1]],[[1,1,1,1,1,2,2]],[[1,1,1,1,1,3,1]],[[1,1,1,1,2],[2]],[[1,1,1,1,2],[3]],[[1,1,1,1,2,1,1]],[[1,1,1,1,2,1,2]]]

theorem patterns_17_8_50_verified : ∀ D ∈ patterns_17_8_50, PatternVerified 17 8 D := by

  simp only [patterns_17_8_50, List.forall_mem_cons]

  exact ⟨⟨certificate_3020, certificate_3020_valid⟩, ⟨⟨certificate_3021, certificate_3021_valid⟩, ⟨⟨certificate_3022, certificate_3022_valid⟩, ⟨⟨certificate_3023, certificate_3023_valid⟩, ⟨⟨certificate_3024, certificate_3024_valid⟩, ⟨⟨certificate_3025, certificate_3025_valid⟩, ⟨⟨certificate_3026, certificate_3026_valid⟩, ⟨⟨certificate_3027, certificate_3027_valid⟩, ⟨⟨certificate_3028, certificate_3028_valid⟩, ⟨⟨certificate_3029, certificate_3029_valid⟩, ⟨⟨certificate_3030, certificate_3030_valid⟩, ⟨⟨certificate_3031, certificate_3031_valid⟩, ⟨⟨certificate_3032, certificate_3032_valid⟩, ⟨⟨certificate_3033, certificate_3033_valid⟩, ⟨⟨certificate_3034, certificate_3034_valid⟩, ⟨⟨certificate_3035, certificate_3035_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_51 : List (List (List ℕ)) := [[[1,1,1,1,2,2,1]],[[1,1,1,1,3],[2]],[[1,1,1,1,3,1,1]],[[1,1,1,2],[1,2]],[[1,1,1,2],[1,3]],[[1,1,1,2],[2,2]],[[1,1,1,2,1],[2]],[[1,1,1,2,1],[3]],[[1,1,1,2,1,1,1]],[[1,1,1,2,1,1,2]],[[1,1,1,2,1,2,1]],[[1,1,1,2,2],[2]],[[1,1,1,2,2,1,1]],[[1,1,1,3],[1,2]],[[1,1,1,3,1],[2]],[[1,1,1,3,1,1,1]]]

theorem patterns_17_8_51_verified : ∀ D ∈ patterns_17_8_51, PatternVerified 17 8 D := by

  simp only [patterns_17_8_51, List.forall_mem_cons]

  exact ⟨⟨certificate_3036, certificate_3036_valid⟩, ⟨⟨certificate_3037, certificate_3037_valid⟩, ⟨⟨certificate_3038, certificate_3038_valid⟩, ⟨⟨certificate_3039, certificate_3039_valid⟩, ⟨⟨certificate_3040, certificate_3040_valid⟩, ⟨⟨certificate_3041, certificate_3041_valid⟩, ⟨⟨certificate_3042, certificate_3042_valid⟩, ⟨⟨certificate_3043, certificate_3043_valid⟩, ⟨⟨certificate_3044, certificate_3044_valid⟩, ⟨⟨certificate_3045, certificate_3045_valid⟩, ⟨⟨certificate_3046, certificate_3046_valid⟩, ⟨⟨certificate_3047, certificate_3047_valid⟩, ⟨⟨certificate_3048, certificate_3048_valid⟩, ⟨⟨certificate_3049, certificate_3049_valid⟩, ⟨⟨certificate_3050, certificate_3050_valid⟩, ⟨⟨certificate_3051, certificate_3051_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_52 : List (List (List ℕ)) := [[[1,1,2],[1,1,2]],[[1,1,2],[1,1,3]],[[1,1,2],[1,2,1]],[[1,1,2],[1,2,2]],[[1,1,2],[1,3,1]],[[1,1,2],[2],[2]],[[1,1,2],[2],[3]],[[1,1,2],[2,1,2]],[[1,1,2,1],[1,2]],[[1,1,2,1],[1,3]],[[1,1,2,1],[2,2]],[[1,1,2,1,1],[2]],[[1,1,2,1,1],[3]],[[1,1,2,1,1,1,2]],[[1,1,2,1,1,2,1]],[[1,1,2,1,2],[2]]]

theorem patterns_17_8_52_verified : ∀ D ∈ patterns_17_8_52, PatternVerified 17 8 D := by

  simp only [patterns_17_8_52, List.forall_mem_cons]

  exact ⟨⟨certificate_3052, certificate_3052_valid⟩, ⟨⟨certificate_3053, certificate_3053_valid⟩, ⟨⟨certificate_3054, certificate_3054_valid⟩, ⟨⟨certificate_3055, certificate_3055_valid⟩, ⟨⟨certificate_3056, certificate_3056_valid⟩, ⟨⟨certificate_3057, certificate_3057_valid⟩, ⟨⟨certificate_3058, certificate_3058_valid⟩, ⟨⟨certificate_3059, certificate_3059_valid⟩, ⟨⟨certificate_3060, certificate_3060_valid⟩, ⟨⟨certificate_3061, certificate_3061_valid⟩, ⟨⟨certificate_3062, certificate_3062_valid⟩, ⟨⟨certificate_3063, certificate_3063_valid⟩, ⟨⟨certificate_3064, certificate_3064_valid⟩, ⟨⟨certificate_3065, certificate_3065_valid⟩, ⟨⟨certificate_3066, certificate_3066_valid⟩, ⟨⟨certificate_3067, certificate_3067_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_53 : List (List (List ℕ)) := [[[1,1,2,1,2,1,1]],[[1,1,2,2],[1,2]],[[1,1,2,2,1],[2]],[[1,1,3],[1,2,1]],[[1,1,3],[2],[2]],[[1,1,3,1],[1,2]],[[1,1,3,1,1],[2]],[[1,2],[1,2],[2]],[[1,2],[1,2],[3]],[[1,2],[1,2,1,2]],[[1,2],[1,2,2,1]],[[1,2],[1,3],[2]],[[1,2],[2],[2,2]],[[1,2],[2,1,1,2]],[[1,2,1],[1,2,1]],[[1,2,1],[1,2,2]]]

theorem patterns_17_8_53_verified : ∀ D ∈ patterns_17_8_53, PatternVerified 17 8 D := by

  simp only [patterns_17_8_53, List.forall_mem_cons]

  exact ⟨⟨certificate_3068, certificate_3068_valid⟩, ⟨⟨certificate_3069, certificate_3069_valid⟩, ⟨⟨certificate_3070, certificate_3070_valid⟩, ⟨⟨certificate_3071, certificate_3071_valid⟩, ⟨⟨certificate_3072, certificate_3072_valid⟩, ⟨⟨certificate_3073, certificate_3073_valid⟩, ⟨⟨certificate_3074, certificate_3074_valid⟩, ⟨⟨certificate_3075, certificate_3075_valid⟩, ⟨⟨certificate_3076, certificate_3076_valid⟩, ⟨⟨certificate_3077, certificate_3077_valid⟩, ⟨⟨certificate_3078, certificate_3078_valid⟩, ⟨⟨certificate_3079, certificate_3079_valid⟩, ⟨⟨certificate_3080, certificate_3080_valid⟩, ⟨⟨certificate_3081, certificate_3081_valid⟩, ⟨⟨certificate_3082, certificate_3082_valid⟩, ⟨⟨certificate_3083, certificate_3083_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8_54 : List (List (List ℕ)) := [[[1,2,1],[1,3,1]],[[1,2,1],[2],[2]],[[1,2,1],[2],[3]],[[1,2,1],[2,1,2]],[[1,2,1,1,1,1,2]],[[1,2,1,1,1,2,1]],[[1,2,1,1,2],[2]],[[1,2,1,2,1],[2]],[[1,2,2],[2],[2]],[[1,3,1],[2],[2]],[[2],[2],[2],[2]],[[2],[2],[2],[3]],[[2],[2],[2,1,2]],[[2],[2,1,1,1,2]],[[2,1,1,1,1,1,2]]]

theorem patterns_17_8_54_verified : ∀ D ∈ patterns_17_8_54, PatternVerified 17 8 D := by

  simp only [patterns_17_8_54, List.forall_mem_cons]

  exact ⟨⟨certificate_3084, certificate_3084_valid⟩, ⟨⟨certificate_3085, certificate_3085_valid⟩, ⟨⟨certificate_3086, certificate_3086_valid⟩, ⟨⟨certificate_3087, certificate_3087_valid⟩, ⟨⟨certificate_3088, certificate_3088_valid⟩, ⟨⟨certificate_3089, certificate_3089_valid⟩, ⟨⟨certificate_3090, certificate_3090_valid⟩, ⟨⟨certificate_3091, certificate_3091_valid⟩, ⟨⟨certificate_3092, certificate_3092_valid⟩, ⟨⟨certificate_3093, certificate_3093_valid⟩, ⟨⟨certificate_3094, certificate_3094_valid⟩, ⟨⟨certificate_3095, certificate_3095_valid⟩, ⟨⟨certificate_3096, certificate_3096_valid⟩, ⟨⟨certificate_3097, certificate_3097_valid⟩, ⟨⟨certificate_3098, certificate_3098_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_17_8 : List (List (List ℕ)) := patterns_17_8_0 ++ (patterns_17_8_1 ++ (patterns_17_8_2 ++ (patterns_17_8_3 ++ (patterns_17_8_4 ++ (patterns_17_8_5 ++ (patterns_17_8_6 ++ (patterns_17_8_7 ++ (patterns_17_8_8 ++ (patterns_17_8_9 ++ (patterns_17_8_10 ++ (patterns_17_8_11 ++ (patterns_17_8_12 ++ (patterns_17_8_13 ++ (patterns_17_8_14 ++ (patterns_17_8_15 ++ (patterns_17_8_16 ++ (patterns_17_8_17 ++ (patterns_17_8_18 ++ (patterns_17_8_19 ++ (patterns_17_8_20 ++ (patterns_17_8_21 ++ (patterns_17_8_22 ++ (patterns_17_8_23 ++ (patterns_17_8_24 ++ (patterns_17_8_25 ++ (patterns_17_8_26 ++ (patterns_17_8_27 ++ (patterns_17_8_28 ++ (patterns_17_8_29 ++ (patterns_17_8_30 ++ (patterns_17_8_31 ++ (patterns_17_8_32 ++ (patterns_17_8_33 ++ (patterns_17_8_34 ++ (patterns_17_8_35 ++ (patterns_17_8_36 ++ (patterns_17_8_37 ++ (patterns_17_8_38 ++ (patterns_17_8_39 ++ (patterns_17_8_40 ++ (patterns_17_8_41 ++ (patterns_17_8_42 ++ (patterns_17_8_43 ++ (patterns_17_8_44 ++ (patterns_17_8_45 ++ (patterns_17_8_46 ++ (patterns_17_8_47 ++ (patterns_17_8_48 ++ (patterns_17_8_49 ++ (patterns_17_8_50 ++ (patterns_17_8_51 ++ (patterns_17_8_52 ++ (patterns_17_8_53 ++ (patterns_17_8_54 ++ ([])))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem patterns_17_8_verified : ∀ D ∈ patterns_17_8, PatternVerified 17 8 D := by

  simp only [patterns_17_8, List.forall_mem_append]

  exact ⟨patterns_17_8_0_verified, ⟨patterns_17_8_1_verified, ⟨patterns_17_8_2_verified, ⟨patterns_17_8_3_verified, ⟨patterns_17_8_4_verified, ⟨patterns_17_8_5_verified, ⟨patterns_17_8_6_verified, ⟨patterns_17_8_7_verified, ⟨patterns_17_8_8_verified, ⟨patterns_17_8_9_verified, ⟨patterns_17_8_10_verified, ⟨patterns_17_8_11_verified, ⟨patterns_17_8_12_verified, ⟨patterns_17_8_13_verified, ⟨patterns_17_8_14_verified, ⟨patterns_17_8_15_verified, ⟨patterns_17_8_16_verified, ⟨patterns_17_8_17_verified, ⟨patterns_17_8_18_verified, ⟨patterns_17_8_19_verified, ⟨patterns_17_8_20_verified, ⟨patterns_17_8_21_verified, ⟨patterns_17_8_22_verified, ⟨patterns_17_8_23_verified, ⟨patterns_17_8_24_verified, ⟨patterns_17_8_25_verified, ⟨patterns_17_8_26_verified, ⟨patterns_17_8_27_verified, ⟨patterns_17_8_28_verified, ⟨patterns_17_8_29_verified, ⟨patterns_17_8_30_verified, ⟨patterns_17_8_31_verified, ⟨patterns_17_8_32_verified, ⟨patterns_17_8_33_verified, ⟨patterns_17_8_34_verified, ⟨patterns_17_8_35_verified, ⟨patterns_17_8_36_verified, ⟨patterns_17_8_37_verified, ⟨patterns_17_8_38_verified, ⟨patterns_17_8_39_verified, ⟨patterns_17_8_40_verified, ⟨patterns_17_8_41_verified, ⟨patterns_17_8_42_verified, ⟨patterns_17_8_43_verified, ⟨patterns_17_8_44_verified, ⟨patterns_17_8_45_verified, ⟨patterns_17_8_46_verified, ⟨patterns_17_8_47_verified, ⟨patterns_17_8_48_verified, ⟨patterns_17_8_49_verified, ⟨patterns_17_8_50_verified, ⟨patterns_17_8_51_verified, ⟨patterns_17_8_52_verified, ⟨patterns_17_8_53_verified, ⟨patterns_17_8_54_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_17_8_coverage : patternChoices 8 9 [] = patterns_17_8 := by decide +kernel

theorem finite_patterns_17_8 : ∀ D ∈ patternChoices 8 (17-8) [], PatternVerified 17 8 D := by

  rw [patterns_17_8_coverage]

  exact patterns_17_8_verified

end CycleClique

end OAI
